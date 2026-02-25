
#define ltable_c
#define LUA_CORE

#include "lprefix.h"
#include <math.h>
#include <stddef.h>
#include <string.h>
#include "lua.h"
#include "ldebug.h"
#include "ldo.h"
#include "lgc.h"
#include "lmem.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "lvm.h"

#define MAXABITS	cast_int(sizeof(int) * CHAR_BIT - 1)
#define MAXASIZE	(1u << MAXABITS)
#define hashpow2(t,n)		(gnode(t, lmod((n), sizenode(t))))
#define hashstr(t,str)		hashpow2(t, (str)->hash)
#define hashboolean(t,p)	hashpow2(t, p)
#define hashint(t,i)		hashpow2(t, i)
#define hashmod(t,n)	(gnode(t, ((n) % ((sizenode(t)-1)|1))))
#define hashpointer(t,p)	hashmod(t, point2uint(p))

#define dummynode		(&dummynode_)

static const Node dummynode_ = {
  {NILCONSTANT},  /* value */
  {{NILCONSTANT, 0}}  /* key */
};

#define isdummy(n)		((n) == dummynode)

static Node *mainposition (const Table *t, const TValue *key) {
  switch (ttype(key)) {
    case LUA_TNUMINT: return hashint(t, ivalue(key));
    case LUA_TNUMFLT: {
      lua_Integer k;
      if (luaV_tointeger(key, &k, 0)) return hashint(t, k);
      else return hashmod(t, cast_int(fltvalue(key)));
    }
    case LUA_TSHRSTR: return hashstr(t, tsvalue(key));
    case LUA_TLNGSTR: return hashpow2(t, luaS_hashlongstr(tsvalue(key)));
    case LUA_TBOOLEAN: return hashboolean(t, bvalue(key));
    case LUA_TLIGHTUSERDATA: return hashpointer(t, pvalue(key));
    case LUA_TLCF: return hashpointer(t, fvalue(key));
    default: return hashpointer(t, gcvalue(key));
  }
}

static int arrayindex (const TValue *key) {
  if (ttisinteger(key)) {
    lua_Integer k = ivalue(key);
    if (0 < k && (lua_Unsigned)k <= MAXASIZE) return cast_int(k);
  }
  return 0;
}

static int findindex (lua_State *L, Table *t, StkId key) {
  int i;
  if (ttisnil(key)) return 0;
  i = arrayindex(key);
  if (0 < i && i <= cast_int(t->sizearray)) return i;
  else {
    int nx;
    Node *n = mainposition(t, key);
    for (;;) {
      if (luaV_rawequalobj(gkey(n), key) ||
            (ttisdeadkey(gkey(n)) && iscollectable(key) &&
             gcvalue(gkey(n)) == gcvalue(key))) {
        i = cast_int(n - gnode(t, 0));
        return i + 1 + cast_int(t->sizearray);
      }
      nx = gnext(n);
      if (nx == 0) luaG_runerror(L, "invalid key to 'next'");
      n += nx;
    }
  }
}

int luaH_next (lua_State *L, Table *t, StkId key) {
  unsigned int i = findindex(L, t, key);
  for (; i < t->sizearray; i++) {
    if (t->array_tags[i] != LUA_TNIL) {
      setivalue(key, i + 1);
      TValue *res = key + 1;
      res->value_ = t->array[i];
      res->tt_ = t->array_tags[i];
      return 1;
    }
  }
  for (i -= t->sizearray; cast_int(i) < sizenode(t); i++) {
    if (!ttisnil(gval(gnode(t, i)))) {
      setobj2s(L, key, gkey(gnode(t, i)));
      setobj2s(L, key + 1, gval(gnode(t, i)));
      return 1;
    }
  }
  return 0;
}

static int numusearray (const Table *t, unsigned int *nums) {
  int lg;
  unsigned int ttlg;
  int ause = 0;
  int i = 1;
  for (lg = 0, ttlg = 1; lg <= MAXABITS; lg++, ttlg <<= 1) {
    int lc = 0;
    int lim = ttlg;
    if (lim > cast_int(t->sizearray)) {
      lim = cast_int(t->sizearray);
      if (i > lim) break;
    }
    for (; i <= lim; i++) {
      if (t->array_tags[i-1] != LUA_TNIL) lc++;
    }
    nums[lg] += lc;
    ause += lc;
  }
  return ause;
}

static int numusehash (const Table *t, unsigned int *nums, unsigned int *pna) {
  int ause = 0;
  int i = sizenode(t);
  while (i--) {
    Node *n = &t->node[i];
    if (!ttisnil(gval(n))) {
      ause++;
      *pna += arrayindex(gkey(n));
    }
  }
  (void)nums;
  return ause;
}

static void setarrayvector (lua_State *L, Table *t, unsigned int size) {
  unsigned int i;
  luaM_reallocvector(L, t->array, t->sizearray, size, Value);
  luaM_reallocvector(L, t->array_tags, t->sizearray, size, lu_byte);
  for (i = t->sizearray; i < size; i++) t->array_tags[i] = LUA_TNIL;
  t->sizearray = size;
}

static void setnodevector (lua_State *L, Table *t, unsigned int size) {
  if (size == 0) {
    t->node = cast(Node *, dummynode);
    t->lsizenode = 0;
    t->lastfree = NULL;
  } else {
    int i;
    int lsize = luaO_ceillog2(size);
    if (lsize > MAXABITS) luaG_runerror(L, "table overflow");
    size = twoto(lsize);
    t->node = luaM_newvector(L, size, Node);
    for (i = 0; i < (int)size; i++) {
      Node *n = gnode(t, i);
      gnext(n) = 0;
      setnilvalue(wgkey(n));
      setnilvalue(gval(n));
    }
    t->lsizenode = cast_byte(lsize);
    t->lastfree = gnode(t, size);
  }
}

typedef struct { Table *t; unsigned int nhsize; } AuxsetnodeT;
static void auxsetnode (lua_State *L, void *ud) {
  AuxsetnodeT *asn = cast(AuxsetnodeT *, ud);
  setnodevector(L, asn->t, asn->nhsize);
}

void luaH_resize (lua_State *L, Table *t, unsigned int nasize, unsigned int nhsize) {
  unsigned int i;
  int j;
  AuxsetnodeT asn;
  unsigned int oldasize = t->sizearray;
  int oldhsize = t->lsizenode;
  Node *nold = t->node;
  if (nasize > oldasize) setarrayvector(L, t, nasize);
  asn.t = t; asn.nhsize = nhsize;
  if (luaD_rawrunprotected(L, auxsetnode, &asn) != LUA_OK) {
    setarrayvector(L, t, oldasize);
    luaD_throw(L, LUA_ERRMEM);
  }
  if (nasize < oldasize) {
    t->sizearray = nasize;
    for (i = nasize; i < oldasize; i++) {
      if (t->array_tags[i] != LUA_TNIL) {
        TValue temp; temp.value_ = t->array[i]; temp.tt_ = t->array_tags[i];
        luaH_setint(L, t, i + 1, &temp);
      }
    }
    luaM_reallocvector(L, t->array, oldasize, nasize, Value);
    luaM_reallocvector(L, t->array_tags, oldasize, nasize, lu_byte);
  }
  for (j = twoto(oldhsize) - 1; j >= 0; j--) {
    Node *old = nold + j;
    if (!ttisnil(gval(old))) luaH_set(L, t, gkey(old), gval(old));
  }
  if (!isdummy(nold)) luaM_freearray(L, nold, cast(size_t, twoto(oldhsize)));
}

void luaH_resizearray (lua_State *L, Table *t, unsigned int nasize) {
  int nsize = isdummy(t->node) ? 0 : sizenode(t);
  luaH_resize(L, t, nasize, nsize);
}

static unsigned int computesizes (unsigned int nums[], unsigned int *pna) {
  int i;
  unsigned int twotoi, a = 0, na = 0, optimal = 0;
  for (i = 0, twotoi = 1; twotoi / 2 < *pna; i++, twotoi <<= 1) {
    if (nums[i] > 0) {
      a += nums[i];
      if (a > twotoi / 2) { optimal = twotoi; na = a; }
    }
  }
  *pna = na;
  return optimal;
}

static int countint (const TValue *key, unsigned int *nums) {
  int k = arrayindex(key);
  if (0 < k && k <= (int)MAXASIZE) {
    nums[luaO_ceillog2(k)]++;
    return 1;
  }
  else return 0;
}

static void rehash (lua_State *L, Table *t, const TValue *ek) {
  unsigned int asize, na, nums[MAXABITS + 1];
  int i, totaluse;
  for (i = 0; i <= MAXABITS; i++) nums[i] = 0;
  na = numusearray(t, nums);
  totaluse = na;
  totaluse += numusehash(t, nums, &na);
  na += countint(ek, nums);
  totaluse++;
  asize = computesizes(nums, &na);
  luaH_resize(L, t, asize, totaluse - na);
}

Table *luaH_new (lua_State *L) {
  GCObject *o = luaC_newobj(L, LUA_TTABLE, sizeof(Table));
  Table *t = gco2t(o);
  t->metatable = NULL; t->flags = cast_byte(~0); t->array = NULL; t->array_tags = NULL; t->sizearray = 0; t->type = 0;
  setnodevector(L, t, 0);
  return t;
}

void luaH_free (lua_State *L, Table *t) {
  if (!isdummy(t->node)) luaM_freearray(L, t->node, cast(size_t, sizenode(t)));
  luaM_freearray(L, t->array, t->sizearray);
  luaM_freearray(L, t->array_tags, t->sizearray);
  luaM_free(L, t);
}

static Node *getfreepos (Table *t) {
  while (t->lastfree > t->node) {
    t->lastfree--;
    if (ttisnil(gkey(t->lastfree))) return t->lastfree;
  }
  return NULL;
}

TValue *luaH_newkey (lua_State *L, Table *t, const TValue *key) {
  Node *mp;
  if (ttisnil(key)) luaG_runerror(L, "table index is nil");
  mp = mainposition(t, key);
  if (!ttisnil(gval(mp)) || isdummy(mp)) {
    Node *othern, *f = getfreepos(t);
    if (f == NULL) {
      rehash(L, t, key);
      TValue nilv; setnilvalue(&nilv); luaH_set(L, t, key, &nilv); return cast(TValue *, luaH_get(t, key));
    }
    lua_assert(!isdummy(f));
    othern = mainposition(t, gkey(mp));
    if (othern != mp) {
      while (othern + gnext(othern) != mp) othern += gnext(othern);
      gnext(othern) = cast_int(f - othern);
      *f = *mp;
      if (gnext(mp) != 0) { gnext(f) += cast_int(mp - f); gnext(mp) = 0; }
      setnilvalue(gval(mp));
    } else {
      if (gnext(mp) != 0) gnext(f) = cast_int((mp + gnext(mp)) - f);
      else lua_assert(gnext(f) == 0);
      gnext(mp) = cast_int(f - mp);
      mp = f;
    }
  }
  setnodekey(L, &mp->i_key, key);
  luaC_barrierback(L, t, key);
  return gval(mp);
}

const TValue *luaH_getint (Table *t, lua_Integer key) {
  if (l_castS2U(key) - 1 < t->sizearray) {
    t->scratch_val.value_ = t->array[key - 1]; t->scratch_val.tt_ = t->array_tags[key - 1]; return &t->scratch_val;
  } else {
    Node *n = hashint(t, key);
    for (;;) {
      if (ttisinteger(gkey(n)) && ivalue(gkey(n)) == key) return gval(n);
      int nx = gnext(n); if (nx == 0) break; n += nx;
    }
    return luaO_nilobject;
  }
}

const TValue *luaH_getshortstr (Table *t, TString *key) {
  Node *n = hashstr(t, key);
  for (;;) {
    const TValue *k = gkey(n);
    if (ttisshrstring(k) && eqshrstr(tsvalue(k), key)) return gval(n);
    int nx = gnext(n); if (nx == 0) return luaO_nilobject; n += nx;
  }
}

const TValue *luaH_getstr (Table *t, TString *key) {
  if (key->tt == LUA_TSHRSTR) return luaH_getshortstr(t, key);
  else {
    TValue ko; val_(&ko).gc = obj2gco(key); settt_(&ko, ctb(key->tt));
    Node *n = mainposition(t, &ko);
    for (;;) {
      if (luaV_rawequalobj(gkey(n), &ko)) return gval(n);
      int nx = gnext(n); if (nx == 0) return luaO_nilobject; n += nx;
    }
  }
}

const TValue *luaH_get (Table *t, const TValue *key) {
  switch (ttype(key)) {
    case LUA_TSHRSTR: return luaH_getshortstr(t, tsvalue(key));
    case LUA_TNUMINT: return luaH_getint(t, ivalue(key));
    case LUA_TNIL: return luaO_nilobject;
    case LUA_TNUMFLT: {
      lua_Integer k; if (luaV_tointeger(key, &k, 0)) return luaH_getint(t, k);
    } /* FALLTHROUGH */
    default: {
      Node *n = mainposition(t, key);
      for (;;) {
        if (luaV_rawequalobj(gkey(n), key)) return gval(n);
        int nx = gnext(n); if (nx == 0) return luaO_nilobject; n += nx;
      }
    }
  }
}

void luaH_set (lua_State *L, Table *t, const TValue *key, const TValue *value) {
  lua_Integer k;
  if (ttisinteger(key) || (ttisfloat(key) && luaV_tointeger(key, &k, 0))) {
    lua_Integer idx = ttisinteger(key) ? ivalue(key) : k;
    if (l_castS2U(idx) - 1 < t->sizearray) {
      luaH_setint(L, t, idx, (TValue *)value);
      return;
    }
  }
  const TValue *p = luaH_get(t, key);
  if (p != luaO_nilobject && p != &t->scratch_val) {
    setobj2t(L, cast(TValue *, p), value);
  } else {
    TValue *cell = luaH_newkey(L, t, key);
    setobj2t(L, cell, value);
  }
}

void luaH_setint (lua_State *L, Table *t, lua_Integer key, TValue *value) {
  if (l_castS2U(key) - 1 < t->sizearray) {
    t->array[key - 1] = value->value_; t->array_tags[key - 1] = value->tt_;
    if (iscollectable(value)) luaC_barrierback(L, t, value);
  } else {
    TValue k; setivalue(&k, key); TValue *cell = luaH_newkey(L, t, &k); setobj2t(L, cell, value);
  }
}

static unsigned int unbound_search (Table *t, unsigned int j) {
  unsigned int i = j;
  j++;
  while (!ttisnil(luaH_getint(t, j))) {
    i = j; if (j > cast(unsigned int, MAX_INT)/2) {
      i = 1; while (!ttisnil(luaH_getint(t, i))) i++; return i - 1;
    }
    j *= 2;
  }
  while (j - i > 1) {
    unsigned int m = (i+j)/2; if (ttisnil(luaH_getint(t, m))) j = m; else i = m;
  }
  return i;
}

lua_Unsigned luaH_getn (lua_State *L, Table *t) {
  (void)L; unsigned int j = t->sizearray;
  if (j > 0 && t->array_tags[j - 1] == LUA_TNIL) {
    unsigned int i = 0;
    while (j - i > 1) {
      unsigned int m = (i+j)/2; if (t->array_tags[m - 1] == LUA_TNIL) j = m; else i = m;
    }
    return i;
  }
  else if (isdummy(t->node)) return (lua_Unsigned)j;
  else return (lua_Unsigned)unbound_search(t, j);
}

#if defined(LUA_DEBUG)
Node *luaH_mainposition (const Table *t, const TValue *key) { return mainposition(t, key); }
int luaH_isdummy (Node *n) { return isdummy(n); }
#endif
