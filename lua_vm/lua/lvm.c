/*
** $Id: lvm.c,v 2.268 2016/02/05 19:59:14 roberto Exp $
** Lua virtual machine
** See Copyright Notice in lua.h
*/

#define lvm_c
#define LUA_CORE

#include "lprefix.h"

#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "lgc.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "ltm.h"
#include "lvm.h"
#include "lobfuscator.h"
#include "lapi.h"
#include "lauxlib.h"


/* limit for table tag-method chains (to avoid loops) */
#define MAXTAGLOOP	2000

#define GET_REAL_OPCODE(i, p) ((p)->op_map ? (OpCode)(p)->op_map[GET_OPCODE(i)] : GET_OPCODE(i))



/*
** 'l_intfitsf' checks whether a given integer can be converted to a
** float without rounding. Used in comparisons. Left undefined if
** all integers fit in a float precisely.
*/
#if !defined(l_intfitsf)

/* number of bits in the mantissa of a float */
#define NBM		(l_mathlim(MANT_DIG))

/*
** Check whether some integers may not fit in a float, that is, whether
** (maxinteger >> NBM) > 0 (that implies (1 << NBM) <= maxinteger).
** (The shifts are done in parts to avoid shifting by more than the size
** of an integer. In a worst case, NBM == 113 for long double and
** sizeof(integer) == 32.)
*/
#if ((((LUA_MAXINTEGER >> (NBM / 4)) >> (NBM / 4)) >> (NBM / 4)) \
	>> (NBM - (3 * (NBM / 4))))  >  0

#define l_intfitsf(i)  \
  (-((lua_Integer)1 << NBM) <= (i) && (i) <= ((lua_Integer)1 << NBM))

#endif

#endif



/*
** Try to convert a value to a float. The float case is already handled
** by the macro 'tonumber'.
*/
int luaV_tonumber_ (const TValue *obj, lua_Number *n) {
  TValue v;
  if (ttisinteger(obj)) {
    *n = cast_num(ivalue(obj));
    return 1;
  }
  else if (cvt2num(obj) &&  /* string convertible to number? */
            luaO_str2num(svalue(obj), &v) == vslen(obj) + 1) {
    *n = nvalue(&v);  /* convert result of 'luaO_str2num' to a float */
    return 1;
  }
  else
    return 0;  /* conversion failed */
}


/*
** try to convert a value to an integer, rounding according to 'mode':
** mode == 0: accepts only integral values
** mode == 1: takes the floor of the number
** mode == 2: takes the ceil of the number
*/
int luaV_tointeger (const TValue *obj, lua_Integer *p, int mode) {
  TValue v;
 again:
  if (ttisfloat(obj)) {
    lua_Number n = fltvalue(obj);
    lua_Number f = l_floor(n);
    if (n != f) {  /* not an integral value? */
      if (mode == 0) return 0;  /* fails if mode demands integral value */
      else if (mode > 1)  /* needs ceil? */
        f += 1;  /* convert floor to ceil (remember: n != f) */
    }
    return lua_numbertointeger(f, p);
  }
  else if (ttisinteger(obj)) {
    *p = ivalue(obj);
    return 1;
  }
  else if (cvt2num(obj) &&
            luaO_str2num(svalue(obj), &v) == vslen(obj) + 1) {
    obj = &v;
    goto again;  /* convert result from 'luaO_str2num' to an integer */
  }
  return 0;  /* conversion failed */
}


/*
** Try to convert a 'for' limit to an integer, preserving the
** semantics of the loop.
** (The following explanation assumes a non-negative step; it is valid
** for negative steps mutatis mutandis.)
** If the limit can be converted to an integer, rounding down, that is
** it.
** Otherwise, check whether the limit can be converted to a number.  If
** the number is too large, it is OK to set the limit as LUA_MAXINTEGER,
** which means no limit.  If the number is too negative, the loop
** should not run, because any initial integer value is larger than the
** limit. So, it sets the limit to LUA_MININTEGER. 'stopnow' corrects
** the extreme case when the initial value is LUA_MININTEGER, in which
** case the LUA_MININTEGER limit would still run the loop once.
*/
static int forlimit (const TValue *obj, lua_Integer *p, lua_Integer step,
                     int *stopnow) {
  *stopnow = 0;  /* usually, let loops run */
  if (!luaV_tointeger(obj, p, (step < 0 ? 2 : 1))) {  /* not fit in integer? */
    lua_Number n;  /* try to convert to float */
    if (!tonumber(obj, &n)) /* cannot convert to float? */
      return 0;  /* not a number */
    if (luai_numlt(0, n)) {  /* if true, float is larger than max integer */
      *p = LUA_MAXINTEGER;
      if (step < 0) *stopnow = 1;
    }
    else {  /* float is smaller than min integer */
      *p = LUA_MININTEGER;
      if (step >= 0) *stopnow = 1;
    }
  }
  return 1;
}


/*
** Finish the table access 'val = t[key]'.
** if 'slot' is NULL, 't' is not a table; otherwise, 'slot' points to
** t[k] entry (which must be nil).
*/
void luaV_finishget (lua_State *L, const TValue *t, TValue *key, StkId val,
                      const TValue *slot) {
  int loop;  /* counter to avoid infinite loops */
  const TValue *tm;  /* metamethod */
  for (loop = 0; loop < MAXTAGLOOP; loop++) {
    if (slot == NULL) {  /* 't' is not a table? */
      lua_assert(!ttistable(t));
      tm = luaT_gettmbyobj(L, t, TM_INDEX);
      if (ttisnil(tm))
        luaG_typeerror(L, t, "索引");  /* no metamethod */
      /* else will try the metamethod */
    }
    else {  /* 't' is a table */
      lua_assert(ttisnil(slot));
      tm = fasttm(L, hvalue(t)->metatable, TM_INDEX);  /* table's metamethod */
      if (tm == NULL) {  /* no metamethod? */
        setnilvalue(val);  /* result is nil */
        return;
      }
      /* else will try the metamethod */
    }
    if (ttisfunction(tm)) {  /* is metamethod a function? */
      luaT_callTM(L, tm, t, key, val, 1);  /* call it */
      return;
    }
    t = tm;  /* else try to access 'tm[key]' */
    if (luaV_fastget(L,t,key,slot,luaH_get)) {  /* fast track? */
      setobj2s(L, val, slot);  /* done */
      return;
    }
    /* else repeat (tail call 'luaV_finishget') */
  }
  luaG_runerror(L, "'__index' 链太长；可能存在循环");
}


/*
** Finish a table assignment 't[key] = val'.
** If 'slot' is NULL, 't' is not a table.  Otherwise, 'slot' points
** to the entry 't[key]', or to 'luaO_nilobject' if there is no such
** entry.  (The value at 'slot' must be nil, otherwise 'luaV_fastset'
** would have done the job.)
*/
void luaV_finishset (lua_State *L, const TValue *t, TValue *key,
                     StkId val, const TValue *slot) {
  int loop;  /* counter to avoid infinite loops */
  for (loop = 0; loop < MAXTAGLOOP; loop++) {
    const TValue *tm;  /* '__newindex' metamethod */
    if (slot != NULL) {  /* is 't' a table? */
      Table *h = hvalue(t);  /* save 't' table */
      lua_assert(ttisnil(slot));  /* old value must be nil */
      tm = fasttm(L, h->metatable, TM_NEWINDEX);  /* get metamethod */
      if (tm == NULL) {  /* no metamethod? */
        if (slot == luaO_nilobject)  /* no previous entry? */
          slot = luaH_newkey(L, h, key);  /* create one */
        /* no metamethod and (now) there is an entry with given key */
        if (slot == &h->scratch_val) luaH_setint(L, h, ivalue(key), val);
        else setobj2t(L, cast(TValue *, slot), val);
        invalidateTMcache(h);
        luaC_barrierback(L, h, val);
        return;
      }
      /* else will try the metamethod */
    }
    else {  /* not a table; check metamethod */
      if (ttisnil(tm = luaT_gettmbyobj(L, t, TM_NEWINDEX)))
        luaG_typeerror(L, t, "索引");
    }
    /* try the metamethod */
    if (ttisfunction(tm)) {
      luaT_callTM(L, tm, t, key, val, 0);
      return;
    }
    t = tm;  /* else repeat assignment over 'tm' */
    if (luaV_fastset(L, t, key, slot, luaH_get, val))
      return;  /* done */
    /* else loop */
  }
  luaG_runerror(L, "'__newindex' 链太长；可能存在循环");
}


/*
** Compare two strings 'ls' x 'rs', returning an integer smaller-equal-
** -larger than zero if 'ls' is smaller-equal-larger than 'rs'.
** The code is a little tricky because it allows '\0' in the strings
** and it uses 'strcoll' (to respect locales) for each segments
** of the strings.
*/
static int l_strcmp (const TString *ls, const TString *rs) {
  const char *l = getstr(ls);
  size_t ll = tsslen(ls);
  const char *r = getstr(rs);
  size_t lr = tsslen(rs);
  for (;;) {  /* for each segment */
    int temp = strcoll(l, r);
    if (temp != 0)  /* not equal? */
      return temp;  /* done */
    else {  /* strings are equal up to a '\0' */
      size_t len = strlen(l);  /* index of first '\0' in both strings */
      if (len == lr)  /* 'rs' is finished? */
        return (len == ll) ? 0 : 1;  /* check 'ls' */
      else if (len == ll)  /* 'ls' is finished? */
        return -1;  /* 'ls' is smaller than 'rs' ('rs' is not finished) */
      /* both strings longer than 'len'; go on comparing after the '\0' */
      len++;
      l += len; ll -= len; r += len; lr -= len;
    }
  }
}


/*
** Check whether integer 'i' is less than float 'f'. If 'i' has an
** exact representation as a float ('l_intfitsf'), compare numbers as
** floats. Otherwise, if 'f' is outside the range for integers, result
** is trivial. Otherwise, compare them as integers. (When 'i' has no
** float representation, either 'f' is "far away" from 'i' or 'f' has
** no precision left for a fractional part; either way, how 'f' is
** truncated is irrelevant.) When 'f' is NaN, comparisons must result
** in false.
*/
static int LTintfloat (lua_Integer i, lua_Number f) {
#if defined(l_intfitsf)
  if (!l_intfitsf(i)) {
    if (f >= -cast_num(LUA_MININTEGER))  /* -minint == maxint + 1 */
      return 1;  /* f >= maxint + 1 > i */
    else if (f > cast_num(LUA_MININTEGER))  /* minint < f <= maxint ? */
      return (i < cast(lua_Integer, f));  /* compare them as integers */
    else  /* f <= minint <= i (or 'f' is NaN)  -->  not(i < f) */
      return 0;
  }
#endif
  return luai_numlt(cast_num(i), f);  /* compare them as floats */
}


/*
** Check whether integer 'i' is less than or equal to float 'f'.
** See comments on previous function.
*/
static int LEintfloat (lua_Integer i, lua_Number f) {
#if defined(l_intfitsf)
  if (!l_intfitsf(i)) {
    if (f >= -cast_num(LUA_MININTEGER))  /* -minint == maxint + 1 */
      return 1;  /* f >= maxint + 1 > i */
    else if (f >= cast_num(LUA_MININTEGER))  /* minint <= f <= maxint ? */
      return (i <= cast(lua_Integer, f));  /* compare them as integers */
    else  /* f < minint <= i (or 'f' is NaN)  -->  not(i <= f) */
      return 0;
  }
#endif
  return luai_numle(cast_num(i), f);  /* compare them as floats */
}


/*
** Return 'l < r', for numbers.
*/
static int LTnum (const TValue *l, const TValue *r) {
  if (ttisinteger(l)) {
    lua_Integer li = ivalue(l);
    if (ttisinteger(r))
      return li < ivalue(r);  /* both are integers */
    else  /* 'l' is int and 'r' is float */
      return LTintfloat(li, fltvalue(r));  /* l < r ? */
  }
  else {
    lua_Number lf = fltvalue(l);  /* 'l' must be float */
    if (ttisfloat(r))
      return luai_numlt(lf, fltvalue(r));  /* both are float */
    else if (luai_numisnan(lf))  /* 'r' is int and 'l' is float */
      return 0;  /* NaN < i is always false */
    else  /* without NaN, (l < r)  <-->  not(r <= l) */
      return !LEintfloat(ivalue(r), lf);  /* not (r <= l) ? */
  }
}


/*
** Return 'l <= r', for numbers.
*/
static int LEnum (const TValue *l, const TValue *r) {
  if (ttisinteger(l)) {
    lua_Integer li = ivalue(l);
    if (ttisinteger(r))
      return li <= ivalue(r);  /* both are integers */
    else  /* 'l' is int and 'r' is float */
      return LEintfloat(li, fltvalue(r));  /* l <= r ? */
  }
  else {
    lua_Number lf = fltvalue(l);  /* 'l' must be float */
    if (ttisfloat(r))
      return luai_numle(lf, fltvalue(r));  /* both are float */
    else if (luai_numisnan(lf))  /* 'r' is int and 'l' is float */
      return 0;  /*  NaN <= i is always false */
    else  /* without NaN, (l <= r)  <-->  not(r < l) */
      return !LTintfloat(ivalue(r), lf);  /* not (r < l) ? */
  }
}


/*
** Main operation less than; return 'l < r'.
*/
int luaV_lessthan (lua_State *L, const TValue *l, const TValue *r) {
  int res;
  if (ttisnumber(l) && ttisnumber(r))  /* both operands are numbers? */
    return LTnum(l, r);
  else if (ttisstring(l) && ttisstring(r))  /* both are strings? */
    return l_strcmp(tsvalue(l), tsvalue(r)) < 0;
  else if ((res = luaT_callorderTM(L, l, r, TM_LT)) < 0)  /* no metamethod? */
    luaG_ordererror(L, l, r);  /* error */
  return res;
}


/*
** Main operation less than or equal to; return 'l <= r'. If it needs
** a metamethod and there is no '__le', try '__lt', based on
** l <= r iff !(r < l) (assuming a total order). If the metamethod
** yields during this substitution, the continuation has to know
** about it (to negate the result of r<l); bit CIST_LEQ in the call
** status keeps that information.
*/
int luaV_lessequal (lua_State *L, const TValue *l, const TValue *r) {
  int res;
  if (ttisnumber(l) && ttisnumber(r))  /* both operands are numbers? */
    return LEnum(l, r);
  else if (ttisstring(l) && ttisstring(r))  /* both are strings? */
    return l_strcmp(tsvalue(l), tsvalue(r)) <= 0;
  else if ((res = luaT_callorderTM(L, l, r, TM_LE)) >= 0)  /* try 'le' */
    return res;
  else {  /* try 'lt': */
    L->ci->callstatus |= CIST_LEQ;  /* mark it is doing 'lt' for 'le' */
    res = luaT_callorderTM(L, r, l, TM_LT);
    L->ci->callstatus ^= CIST_LEQ;  /* clear mark */
    if (res < 0)
      luaG_ordererror(L, l, r);
    return !res;  /* result is negated */
  }
}


/*
** Main operation for equality of Lua values; return 't1 == t2'.
** L == NULL means raw equality (no metamethods)
*/
int luaV_equalobj (lua_State *L, const TValue *t1, const TValue *t2) {
  const TValue *tm;
  if (ttype(t1) != ttype(t2)) {  /* not the same variant? */
    if (ttnov(t1) != ttnov(t2) || ttnov(t1) != LUA_TNUMBER)
      return 0;  /* only numbers can be equal with different variants */
    else {  /* two numbers with different variants */
      lua_Integer i1, i2;  /* compare them as integers */
      return (tointeger(t1, &i1) && tointeger(t2, &i2) && i1 == i2);
    }
  }
  /* values have same type and same variant */
  switch (ttype(t1)) {
    case LUA_TNIL: return 1;
    case LUA_TNUMINT: return (ivalue(t1) == ivalue(t2));
    case LUA_TNUMFLT: return luai_numeq(fltvalue(t1), fltvalue(t2));
    case LUA_TBOOLEAN: return bvalue(t1) == bvalue(t2);  /* true must be 1 !! */
    case LUA_TLIGHTUSERDATA: return pvalue(t1) == pvalue(t2);
    case LUA_TLCF: return fvalue(t1) == fvalue(t2);
    case LUA_TSHRSTR: return eqshrstr(tsvalue(t1), tsvalue(t2));
    case LUA_TLNGSTR: return luaS_eqlngstr(tsvalue(t1), tsvalue(t2));
    case LUA_TUSERDATA: {
      if (uvalue(t1) == uvalue(t2)) return 1;
      else if (L == NULL) return 0;
      tm = fasttm(L, uvalue(t1)->metatable, TM_EQ);
      if (tm == NULL)
        tm = fasttm(L, uvalue(t2)->metatable, TM_EQ);
      break;  /* will try TM */
    }
    case LUA_TTABLE: {
      if (hvalue(t1) == hvalue(t2)) return 1;
      else if (L == NULL) return 0;
      tm = fasttm(L, hvalue(t1)->metatable, TM_EQ);
      if (tm == NULL)
        tm = fasttm(L, hvalue(t2)->metatable, TM_EQ);
      break;  /* will try TM */
    }
    default:
      return gcvalue(t1) == gcvalue(t2);
  }
  if (tm == NULL)  /* no TM? */
    return 0;  /* objects are different */
  luaT_callTM(L, tm, t1, t2, L->top, 1);  /* call TM */
  return !l_isfalse(L->top);
}


/* macro used by 'luaV_concat' to ensure that element at 'o' is a string */
#define tostring(L,o)  \
	(ttisstring(o) || (cvt2str(o) && (luaO_tostring(L, o), 1)))

#define isemptystr(o)	(ttisshrstring(o) && tsvalue(o)->shrlen == 0)

/* copy strings in stack from top - n up to top - 1 to buffer */
static void copy2buff (StkId top, int n, char *buff) {
  size_t tl = 0;  /* size already copied */
  do {
    size_t l = vslen(top - n);  /* length of string being copied */
    memcpy(buff + tl, svalue(top - n), l * sizeof(char));
    tl += l;
  } while (--n > 0);
}


/*
** Main operation for concatenation: concat 'total' values in the stack,
** from 'L->top - total' up to 'L->top - 1'.
*/
void luaV_concat (lua_State *L, int total) {
  lua_assert(total >= 2);
  do {
    StkId top = L->top;
    int n = 2;  /* number of elements handled in this pass (at least 2) */
    if (!(ttisstring(top-2) || cvt2str(top-2)) || !tostring(L, top-1))
      luaT_trybinTM(L, top-2, top-1, top-2, TM_CONCAT);
    else if (isemptystr(top - 1))  /* second operand is empty? */
      cast_void(tostring(L, top - 2));  /* result is first operand */
    else if (isemptystr(top - 2)) {  /* first operand is an empty string? */
      setobjs2s(L, top - 2, top - 1);  /* result is second op. */
    }
    else {
      /* at least two non-empty string values; get as many as possible */
      size_t tl = vslen(top - 1);
      TString *ts;
      /* collect total length and number of strings */
      for (n = 1; n < total && tostring(L, top - n - 1); n++) {
        size_t l = vslen(top - n - 1);
        if (l >= (MAX_SIZE/sizeof(char)) - tl)
          luaG_runerror(L, "字符串长度溢出");
        tl += l;
      }
      if (tl <= LUAI_MAXSHORTLEN) {  /* is result a short string? */
        char buff[LUAI_MAXSHORTLEN];
        copy2buff(top, n, buff);  /* copy strings to buffer */
        ts = luaS_newlstr(L, buff, tl);
      }
      else {  /* long string; copy strings directly to final result */
        ts = luaS_createlngstrobj(L, tl);
        copy2buff(top, n, getstr(ts));
      }
      setsvalue2s(L, top - n, ts);  /* create result */
    }
    total -= n-1;  /* got 'n' strings to create 1 new */
    L->top -= n-1;  /* popped 'n' strings and pushed one */
  } while (total > 1);  /* repeat until only 1 result left */
}


/*
** Main operation 'ra' = #rb'.
*/
void luaV_objlen (lua_State *L, StkId ra, const TValue *rb) {
  const TValue *tm;
  switch (ttype(rb)) {
    case LUA_TTABLE: {
      Table *h = hvalue(rb);
      tm = fasttm(L, h->metatable, TM_LEN);
      if (tm) break;  /* metamethod? break switch to call it */
      setivalue(ra, luaH_getn(L, h));  /* else primitive len */
      return;
    }
    case LUA_TSHRSTR: {
      setivalue(ra, tsvalue(rb)->shrlen);
      return;
    }
    case LUA_TLNGSTR: {
      setivalue(ra, tsvalue(rb)->u.lnglen);
      return;
    }
    default: {  /* try metamethod */
      tm = luaT_gettmbyobj(L, rb, TM_LEN);
      if (ttisnil(tm))  /* no metamethod? */
        luaG_typeerror(L, rb, "取长度");
      break;
    }
  }
  luaT_callTM(L, tm, rb, rb, ra, 1);
}


/*
** Integer division; return 'm // n', that is, floor(m/n).
** C division truncates its result (rounds towards zero).
** 'floor(q) == trunc(q)' when 'q >= 0' or when 'q' is integer,
** otherwise 'floor(q) == trunc(q) - 1'.
*/
lua_Integer luaV_div (lua_State *L, lua_Integer m, lua_Integer n) {
  if (l_castS2U(n) + 1u <= 1u) {  /* special cases: -1 or 0 */
    if (n == 0)
      luaG_runerror(L, "尝试除以零");
    return intop(-, 0, m);   /* n==-1; avoid overflow with 0x80000...//-1 */
  }
  else {
    lua_Integer q = m / n;  /* perform C division */
    if ((m ^ n) < 0 && m % n != 0)  /* 'm/n' would be negative non-integer? */
      q -= 1;  /* correct result for different rounding */
    return q;
  }
}


/*
** Integer modulus; return 'm % n'. (Assume that C '%' with
** negative operands follows C99 behavior. See previous comment
** about luaV_div.)
*/
lua_Integer luaV_mod (lua_State *L, lua_Integer m, lua_Integer n) {
  if (l_castS2U(n) + 1u <= 1u) {  /* special cases: -1 or 0 */
    if (n == 0)
      luaG_runerror(L, "尝试对零取模");
    return 0;   /* m % -1 == 0; avoid overflow with 0x80000...%-1 */
  }
  else {
    lua_Integer r = m % n;
    if (r != 0 && (m ^ n) < 0)  /* 'm/n' would be non-integer negative? */
      r += n;  /* correct result for different rounding */
    return r;
  }
}


/* number of bits in an integer */
#define NBITS	cast_int(sizeof(lua_Integer) * CHAR_BIT)

/*
** Shift left operation. (Shift right just negates 'y'.)
*/
lua_Integer luaV_shiftl (lua_Integer x, lua_Integer y) {
  if (y < 0) {  /* shift right? */
    if (y <= -NBITS) return 0;
    else return intop(>>, x, -y);
  }
  else {  /* shift left */
    if (y >= NBITS) return 0;
    else return intop(<<, x, y);
  }
}


/*
** check whether cached closure in prototype 'p' may be reused, that is,
** whether there is a cached closure with the same upvalues needed by
** new closure to be created.
*/
static LClosure *getcached (Proto *p, UpVal **encup, StkId base) {
  LClosure *c = p->cache;
  if (c != NULL) {  /* is there a cached closure? */
    int nup = p->sizeupvalues;
    Upvaldesc *uv = p->upvalues;
    int i;
    for (i = 0; i < nup; i++) {  /* check whether it has right upvalues */
      TValue *v = uv[i].instack ? base + uv[i].idx : encup[uv[i].idx]->v;
      if (c->upvals[i]->v != v)
        return NULL;  /* wrong upvalue; cannot reuse closure */
    }
  }
  return c;  /* return cached closure (or NULL if no cached closure) */
}


/*
** create a new Lua closure, push it in the stack, and initialize
** its upvalues. Note that the closure is not cached if prototype is
** already black (which means that 'cache' was already cleared by the
** GC).
*/
static void pushclosure (lua_State *L, Proto *p, UpVal **encup, StkId base,
                         StkId ra) {
  int nup = p->sizeupvalues;
  Upvaldesc *uv = p->upvalues;
  int i;
  LClosure *ncl = luaF_newLclosure(L, nup);
  ncl->p = p;
  setclLvalue(L, ra, ncl);  /* anchor new closure in stack */
  for (i = 0; i < nup; i++) {  /* fill in its upvalues */
    if (uv[i].instack)  /* upvalue refers to local variable? */
      ncl->upvals[i] = luaF_findupval(L, base + uv[i].idx);
    else  /* get upvalue from enclosing function */
      ncl->upvals[i] = encup[uv[i].idx];
    ncl->upvals[i]->refcount++;
    /* new closure is white, so we do not need a barrier here */
  }
  if (!isblack(p))  /* cache will not break GC invariant? */
    p->cache = ncl;  /* save it on cache for reuse */
}


/*
** finish execution of an opcode interrupted by an yield
*/
void luaV_finishOp (lua_State *L) {
  CallInfo *ci = L->ci;
  StkId base = ci->u.l.base;
  Instruction inst = *(ci->u.l.savedpc - 1);  /* interrupted instruction */
  Proto *p = clLvalue(ci->func)->p;
  OpCode op = GET_REAL_OPCODE(inst, p);
  switch (op) {  /* finish its execution */
    case OP_ADD: case OP_SUB: case OP_MUL: case OP_DIV: case OP_IDIV:
    case OP_BAND: case OP_BOR: case OP_BXOR: case OP_SHL: case OP_SHR:
    case OP_MOD: case OP_POW:
    case OP_UNM: case OP_BNOT: case OP_LEN:
    case OP_GETTABUP: case OP_GETTABLE: case OP_SELF: {
      setobjs2s(L, base + GETARG_A(inst), --L->top);
      break;
    }
    case OP_LE: case OP_LT: case OP_EQ: {
      int res = !l_isfalse(L->top - 1);
      L->top--;
      if (ci->callstatus & CIST_LEQ) {  /* "<=" using "<" instead? */
        lua_assert(op == OP_LE);
        ci->callstatus ^= CIST_LEQ;  /* clear mark */
        res = !res;  /* negate result */
      }
      lua_assert(GET_REAL_OPCODE(*ci->u.l.savedpc, p) == OP_JMP);
      if (res != GETARG_A(inst))  /* condition failed? */
        ci->u.l.savedpc++;  /* skip jump instruction */
      break;
    }
    case OP_CONCAT: {
      StkId top = L->top - 1;  /* top when 'luaT_trybinTM' was called */
      int b = GETARG_B(inst);      /* first element to concatenate */
      int total = cast_int(top - 1 - (base + b));  /* yet to concatenate */
      setobj2s(L, top - 2, top);  /* put TM result in proper position */
      if (total > 1) {  /* are there elements to concat? */
        L->top = top - 1;  /* top is one after last element (at top-2) */
        luaV_concat(L, total);  /* concat them (may yield again) */
      }
      /* move final result to final position */
      setobj2s(L, ci->u.l.base + GETARG_A(inst), L->top - 1);
      L->top = ci->top;  /* restore top */
      break;
    }
    case OP_TFORCALL: {
      lua_assert(GET_OPCODE(*ci->u.l.savedpc) == OP_TFORLOOP);
      L->top = ci->top;  /* correct top */
      break;
    }
    case OP_CALL: {
      if (GETARG_C(inst) - 1 >= 0)  /* nresults >= 0? */
        L->top = ci->top;  /* adjust results */
      break;
    }
    case OP_TAILCALL: case OP_SETTABUP: case OP_SETTABLE:
      break;
    default: lua_assert(0);
  }
}




/*
** {==================================================================
** Function 'luaV_execute': main interpreter loop
** ===================================================================
*/


/*
** some macros for common tasks in 'luaV_execute'
*/


#define RA(i)	(base+GETARG_A(i))
#define RB(i)	check_exp(getBMode(GET_REAL_OPCODE(i, cl->p)) == OpArgR, base+GETARG_B(i))
#define RC(i)	check_exp(getCMode(GET_REAL_OPCODE(i, cl->p)) == OpArgR, base+GETARG_C(i))

static void decrypt_tv(TValue *o) {
  if (ttisinteger(o)) {
    o->value_.i = DECRYPT_INT(o->value_.i);
  } else if (ttisfloat(o)) {
    // o->value_.n = DECRYPT_FLT_VAL(o->value_.n);
  }
}

static const TValue *get_rk_ptr(TValue *k, int arg, TValue *tmp) {
  const TValue *c = &k[INDEXK(arg)];
  if (ttisnumber(c)) {
    *tmp = *c;
    decrypt_tv(tmp);
    return tmp;
  }
  return c;
}

#define RKB(i)	check_exp(getBMode(GET_REAL_OPCODE(i, cl->p)) == OpArgK, \
	ISK(GETARG_B(i)) ? get_rk_ptr(k, GETARG_B(i), base + cl->p->scratch_base) : base+GETARG_B(i))
#define RKC(i)	check_exp(getCMode(GET_REAL_OPCODE(i, cl->p)) == OpArgK, \
	ISK(GETARG_C(i)) ? get_rk_ptr(k, GETARG_C(i), base + cl->p->scratch_base + 1) : base+GETARG_C(i))


/* execute a jump instruction */
#define dojump(ci,i,e) \
  { int a = GETARG_A(i); \
    if (a != 0) luaF_close(L, ci->u.l.base + a - 1); \
    ci->u.l.savedpc += GETARG_sBx(i) + e; }

/* for test instructions, execute the jump instruction that follows it */
#define donextjump(ci)	{ \
    i = *ci->u.l.savedpc; \
    i = DECRYPT_INST(i, (int)(ci->u.l.savedpc - cl->p->code), cl->p->inst_seed); \
    dojump(ci, i, 1); \
}


#define Protect(x)	{ {x;}; base = ci->u.l.base; ra = RA(i); }

#define checkGC(L,c)  \
	{ luaC_condGC(L, L->top = (c),  /* limit of live values */ \
                         Protect(L->top = ci->top));  /* restore top */ \
           luai_threadyield(L); }


/* fetch an instruction and prepare its execution */
#define vmfetch()	{ \
  __builtin_prefetch(ci->u.l.savedpc + 1, 0, 3); \
  i = *(ci->u.l.savedpc++); \
  i = DECRYPT_INST(i, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed); \
  if (__builtin_expect(L->hookmask & (LUA_MASKLINE | LUA_MASKCOUNT), 0)) \
    Protect(luaG_traceexec(L)); \
  ra = RA(i); /* WARNING: any stack reallocation invalidates 'ra' */ \
  lua_assert(base == ci->u.l.base); \
  lua_assert(base <= L->top && L->top < L->stack + L->stacksize); \
}

#if defined(LUA_USE_JUMP_TABLE)
#define vmdispatch(o)	goto *jump_table[o]
#define vmcase(l)	L_##l:
#define vmbreak		goto L_next_ins
#else
#define vmdispatch(o)	switch(o)
#define vmcase(l)	case l:
#define vmbreak		break
#endif


/*
** copy of 'luaV_gettable', but protecting the call to potential
** metamethod (which can reallocate the stack)
*/
#define gettableProtected(L,t,k,v)  { const TValue *slot; \
  const TValue *rk = (k); \
  if (luaV_fastget(L,t,rk,slot,luaH_get)) { setobj2s(L, v, slot); } \
  else { Protect(luaV_finishget(L,t,cast(TValue *, rk),v,slot)); } }


/* same for 'luaV_settable' */
#define settableProtected(L,t,k,v) { const TValue *slot; \
  const TValue *rk = (k); \
  if (!luaV_fastset(L,t,rk,slot,luaH_get,v)) \
    { Protect(luaV_finishset(L,t,cast(TValue *, rk),v,slot)); } }

#ifdef __ANDROID__
#include <android/log.h>
#define LOG_TAG "lua"
#define LOGD(...) __android_log_print(ANDROID_LOG_INFO, LOG_TAG, __VA_ARGS__)
#endif
static int luaB_next (lua_State *L) {
  luaL_checktype(L, 1, LUA_TTABLE);
  lua_settop(L, 2);  /* create a 2nd argument if there isn't one */
  if (lua_next(L, 1))
    return 2;
  else {
    lua_pushnil(L);
    return 1;
  }
}

void luaV_execute (lua_State *L) {
#if defined(LUA_USE_JUMP_TABLE)
  static const void *const jump_table[NUM_OPCODES] = {
    &&L_OP_MOVE, &&L_OP_LOADK, &&L_OP_LOADKX, &&L_OP_LOADBOOL, &&L_OP_LOADNIL,
    &&L_OP_GETUPVAL, &&L_OP_GETTABUP, &&L_OP_GETTABLE, &&L_OP_SETTABUP, &&L_OP_SETUPVAL,
    &&L_OP_SETTABLE, &&L_OP_NEWTABLE, &&L_OP_SELF, &&L_OP_ADD, &&L_OP_SUB,
    &&L_OP_MUL, &&L_OP_MOD, &&L_OP_POW, &&L_OP_DIV, &&L_OP_IDIV,
    &&L_OP_BAND, &&L_OP_BOR, &&L_OP_BXOR, &&L_OP_SHL, &&L_OP_SHR,
    &&L_OP_UNM, &&L_OP_BNOT, &&L_OP_NOT, &&L_OP_LEN, &&L_OP_CONCAT,
    &&L_OP_JMP, &&L_OP_EQ, &&L_OP_LT, &&L_OP_LE, &&L_OP_TEST,
    &&L_OP_TESTSET, &&L_OP_CALL, &&L_OP_TAILCALL, &&L_OP_RETURN, &&L_OP_FORLOOP,
    &&L_OP_FORPREP, &&L_OP_TFORCALL, &&L_OP_TFORLOOP, &&L_OP_SETLIST, &&L_OP_CLOSURE,
    &&L_OP_VARARG, &&L_OP_EXTRAARG, &&L_OP_TBC, &&L_OP_NEWARRAY, &&L_OP_TFOREACH,
    &&L_OP_TERNARY, &&L_OP_VIRTUAL, &&L_OP_FUSE_GETSUB, &&L_OP_FUSE_GETADD, &&L_OP_FUSE_GETGETSUB, &&L_OP_FAST_DIST, &&L_OP_FUSE_NOP, &&L_OP_FUSE_PARTICLE_DIST,
    &&L_OP_FUSE_ADD_TO_FIELD, &&L_OP_VARARGPREP
  };
#endif
  CallInfo *ci = L->ci;
  LClosure *cl;
  TValue *k;
  StkId base;
  Instruction *vpc = NULL;
  int vcount = 0;
  int vpc_idx = 0;
  ci->callstatus |= CIST_FRESH;  /* fresh invocation of 'luaV_execute" */
  newframe:  /* reentry point when frame changes (call/return) */
  lua_assert(ci == L->ci);
  cl = clLvalue(ci->func);  /* local reference to function's closure */
  k = cl->p->k;  /* local reference to function's constant table */
  base = ci->u.l.base;  /* local copy of function's base */
  vpc = NULL; vcount = 0;
  /* main loop of interpreter */
  for (;;) {
    L_next_ins: {
      Instruction i;
      StkId ra;
      if (__builtin_expect(vpc && vcount > 0, 0)) {
        Instruction raw_i = *vpc++;
        raw_i = DECRYPT_INST(raw_i, vpc_idx++, cl->p->inst_seed);
        /* Decode Custom ISA: OP[0..5] | B[6..14] | A[15..22] | C[23..31] and bitwise NOT */
        Instruction vi = ~raw_i;
        OpCode v_op = (OpCode)(vi & 0x3F);
        int v_b = (vi >> 6) & 0x1FF;
        int v_a = (vi >> 15) & 0xFF;
        int v_c = (vi >> 23) & 0x1FF;
        /* Reconstruct standard instruction bits */
        i = (v_op << POS_OP) | (v_a << POS_A) | (v_b << POS_B) | (v_c << POS_C);
        vcount--;
        ra = RA(i);
      } else {
        vpc = NULL;
        vmfetch();
      }
#if defined(LUA_USE_JUMP_TABLE)
      vmdispatch(GET_REAL_OPCODE(i, cl->p));
#else
      vmdispatch(GET_REAL_OPCODE(i, cl->p)) {
#endif
      vmcase(OP_MOVE) {
        setobjs2s(L, ra, RB(i));
        vmbreak;
      }
      vmcase(OP_LOADK) {
        TValue *rb = k + GETARG_Bx(i);
        setobj2s(L, ra, rb);
        decrypt_tv(ra);
        vmbreak;
      }
      vmcase(OP_LOADKX) {
        TValue *rb;
        Instruction next_i = *ci->u.l.savedpc;
        next_i = DECRYPT_INST(next_i, (int)(ci->u.l.savedpc - cl->p->code), cl->p->inst_seed);
        lua_assert(GET_REAL_OPCODE(next_i, cl->p) == OP_EXTRAARG);
        rb = k + GETARG_Ax(next_i);
        ci->u.l.savedpc++;
        setobj2s(L, ra, rb);
        decrypt_tv(ra);
        vmbreak;
      }
      vmcase(OP_LOADBOOL) {
        setbvalue(ra, GETARG_B(i));
        if (GETARG_C(i)) ci->u.l.savedpc++;  /* skip next instruction (if C) */
        vmbreak;
      }
      vmcase(OP_LOADNIL) {
        int b = GETARG_B(i);
        do {
          setnilvalue(ra++);
        } while (b--);
        vmbreak;
      }
      vmcase(OP_GETUPVAL) {
        int b = GETARG_B(i);
        setobj2s(L, ra, cl->upvals[b]->v);
        vmbreak;
      }
      vmcase(OP_GETTABUP) {
        TValue *upval = cl->upvals[GETARG_B(i)]->v;
        TValue *rc = RKC(i);
        gettableProtected(L, upval, rc, ra);
        vmbreak;
      }
      vmcase(OP_GETTABLE) {
        StkId rb = RB(i);
        TValue *rc = RKC(i);
        if (ttistable(rb) && ttisinteger(rc)) {
            Table *t = hvalue(rb);
            lua_Integer idx = ivalue(rc);
            if (idx > 0 && idx <= t->sizearray) {
                setobj2s(L, ra, luaH_getint(t, idx));
                vmbreak;
            }
        }
        gettableProtected(L, rb, rc, ra);
        vmbreak;
      }
      vmcase(OP_SETTABUP) {
        TValue *upval = cl->upvals[GETARG_A(i)]->v;
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        if(ttistable(ra)) {
            Table *t = hvalue(ra);
            switch (t->type) {
                case 1:
                    if (!ttisinteger(rb))
                        luaG_runerror(L, "数组键必须是整数");
                    break;
                case 2:
                    luaG_runerror(L, "常量表不能被修改");
                    break;
                case 3:
                    luaG_runerror(L, "数组键必须是整数");
                    break;
            }
        }
        settableProtected(L, upval, rb, rc);
        vmbreak;
      }
      vmcase(OP_SETUPVAL) {
        UpVal *uv = cl->upvals[GETARG_B(i)];
        setobj(L, uv->v, ra);
        luaC_upvalbarrier(L, uv);
        vmbreak;
      }
      vmcase(OP_SETTABLE) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        if(ttistable(ra)) {
            Table *t = hvalue(ra);
            switch (t->type) {
                case 1:
                    if (!ttisinteger(rb))
                        luaG_runerror(L, "数组键必须是整数");
                    break;
                case 2:
                    luaG_runerror(L, "常量表不能被修改");
                    break;
                case 3:
                    luaG_runerror(L, "数组键必须是整数");
                    break;
            }
        }
        settableProtected(L, ra, rb, rc);
        vmbreak;
      }
      vmcase(OP_NEWARRAY) {
        int b = GETARG_B(i);
        Table *t = luaH_new(L);
        sethvalue(L, ra, t);
        t->type=1;
        if (b != 0)
          luaH_resize(L, t, luaO_fb2int(b), luaO_fb2int(0));
        checkGC(L, ra + 1);
        vmbreak;
      }
      vmcase(OP_NEWTABLE) {
        int b = GETARG_B(i);
        int c = GETARG_C(i);
        Table *t = luaH_new(L);
        t->type=0;
        sethvalue(L, ra, t);
        if (b != 0 || c != 0)
          luaH_resize(L, t, luaO_fb2int(b), luaO_fb2int(c));
        checkGC(L, ra + 1);
        vmbreak;
      }
      vmcase(OP_SELF) {
        const TValue *aux;
        StkId rb = RB(i);
        TValue *rc = RKC(i);
        TString *key = tsvalue(rc);  /* key must be a string */
        setobjs2s(L, ra + 1, rb);
        if (luaV_fastget(L, rb, key, aux, luaH_getstr)) {
          setobj2s(L, ra, aux);
        }
        else Protect(luaV_finishget(L, rb, rc, ra, aux));
        vmbreak;
      }
      vmcase(OP_ADD) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        if (ttisinteger(rb) && ttisinteger(rc)) {
          setivalue(ra, intop(+, ivalue(rb), ivalue(rc)));
        }
        else {
          lua_Number nb, nc;
          if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
            setfltvalue(ra, luai_numadd(L, nb, nc));
          }
          else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_ADD)); }
        }
        vmbreak;
      }
      vmcase(OP_FUSE_NOP) {
        vmbreak;
      }
      vmcase(OP_FUSE_PARTICLE_DIST) {
        Instruction next_i1 = *ci->u.l.savedpc++;
        next_i1 = DECRYPT_INST(next_i1, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed);
        Instruction next_i2 = *ci->u.l.savedpc++;
        next_i2 = DECRYPT_INST(next_i2, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed);
        int p1_idx = GETARG_B(i);
        int p2_idx = GETARG_C(i);
        int kx_idx = GETARG_Ax(next_i1);
        int ky_idx = GETARG_Ax(next_i2);
        TValue *p1 = base + p1_idx;
        TValue *p2 = base + p2_idx;
        TValue *kx = ISK(kx_idx) ? k + RKASK(kx_idx) : base + kx_idx;
        TValue *ky = ISK(ky_idx) ? k + RKASK(ky_idx) : base + ky_idx;
        TValue v1, v2, v3, v4;

        /* Fast string key lookup */
        if (ttistable(p1) && ttistable(p2) && ttisshrstring(kx) && ttisshrstring(ky)) {
            const TValue *s1 = luaH_getstr(hvalue(p1), tsvalue(kx));
            const TValue *s2 = luaH_getstr(hvalue(p2), tsvalue(kx));
            const TValue *s3 = luaH_getstr(hvalue(p1), tsvalue(ky));
            const TValue *s4 = luaH_getstr(hvalue(p2), tsvalue(ky));
            if (!ttisnil(s1) && !ttisnil(s2) && !ttisnil(s3) && !ttisnil(s4)) {
                lua_Number n1=0, n2=0, n3=0, n4=0;
                if (tonumber(s1, &n1) && tonumber(s2, &n2) && tonumber(s3, &n3) && tonumber(s4, &n4)) {
                    setfltvalue(ra, sqrt((n1-n2)*(n1-n2) + (n3-n4)*(n3-n4)));
                    vmbreak;
                }
            }
        }
        /* Fallback to slow path if needed */
        gettableProtected(L, p1, kx, base + cl->p->scratch_base);
        gettableProtected(L, base + p2_idx, kx, base + cl->p->scratch_base + 1);
        gettableProtected(L, base + p1_idx, ky, base + cl->p->scratch_base + 2);
        gettableProtected(L, base + p2_idx, ky, base + cl->p->scratch_base + 3);
        ra = RA(i);
        StkId tmp = base + cl->p->scratch_base;
        lua_Number n1=0, n2=0, n3=0, n4=0;
        if (tonumber(tmp, &n1) && tonumber(tmp+1, &n2) && tonumber(tmp+2, &n3) && tonumber(tmp+3, &n4)) {
            setfltvalue(ra, sqrt((n1-n2)*(n1-n2) + (n3-n4)*(n3-n4)));
        } else setfltvalue(ra, 0);
        vmbreak;
      }


      vmcase(OP_VARARGPREP) {
        int nfixparams = cl->p->numparams;
        int totalargs = cast_int(L->top - ci->func) - 1;
        if (totalargs < nfixparams) {
          luaD_checkstack(L, nfixparams - totalargs);
          while (totalargs < nfixparams) {
            setnilvalue(L->top++);
            totalargs++;
          }
        }
        if (cl->p->is_vararg == 2) { // Named vararg table
           int nextra = totalargs - (nfixparams - 1);
           if (nextra < 0) nextra = 0;
           Table *t = luaH_new(L);
           sethvalue(L, ci->func + 1 + (nfixparams - 1), t);
           for (int i = 0; i < nextra; i++) {
             luaH_setint(L, t, i + 1, ci->func + 1 + nfixparams + i);
           }
        }
        vmbreak;
      }


      vmcase(OP_FUSE_ADD_TO_FIELD) {
        TValue *t_val = base + GETARG_A(i);
        TValue *rk_key = get_rk_ptr(k, GETARG_B(i), base + cl->p->scratch_base);
        TValue *rk_val = get_rk_ptr(k, GETARG_C(i), base + cl->p->scratch_base + 1);
        if (__builtin_expect(ttistable(t_val), 1)) {
            Table *h = hvalue(t_val);
            TValue *old_field = NULL;
            if (ttisshrstring(rk_key)) old_field = cast(TValue *, luaH_getstr(h, tsvalue(rk_key)));
            else if (ttisinteger(rk_key)) old_field = cast(TValue *, luaH_getint(h, ivalue(rk_key)));

            if (old_field && !ttisnil(old_field) && ttisnumber(old_field) && ttisnumber(rk_val)) {
                if (ttisinteger(old_field) && ttisinteger(rk_val)) {
                    setivalue(old_field, ivalue(old_field) + ivalue(rk_val));
                } else {
                    lua_Number n1 = 0, n2 = 0;
                    tonumber(old_field, &n1);
                    tonumber(rk_val, &n2);
                    setfltvalue(old_field, luai_numadd(L, n1, n2));
                }
                vmbreak;
            }
        }
        /* Fallback */
        TValue temp_res;
        gettableProtected(L, t_val, rk_key, &temp_res);
        if (ttisnumber(&temp_res) && ttisnumber(rk_val)) {
            if (ttisinteger(&temp_res) && ttisinteger(rk_val)) {
                setivalue(&temp_res, ivalue(&temp_res) + ivalue(rk_val));
            } else {
                lua_Number n1 = 0, n2 = 0;
                tonumber(&temp_res, &n1);
                tonumber(rk_val, &n2);
                setfltvalue(&temp_res, luai_numadd(L, n1, n2));
            }
        } else {
            Protect(luaT_trybinTM(L, &temp_res, rk_val, &temp_res, TM_ADD));
        }
        settableProtected(L, t_val, rk_key, &temp_res);
        vmbreak;
      }
      vmcase(OP_SUB) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        if (ttisinteger(rb) && ttisinteger(rc)) {
          setivalue(ra, intop(-, ivalue(rb), ivalue(rc)));
        }
        else {
          lua_Number nb, nc;
          if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
            setfltvalue(ra, luai_numsub(L, nb, nc));
          }
          else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_SUB)); }
        }
        vmbreak;
      }
      vmcase(OP_MUL) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        if (ttisinteger(rb) && ttisinteger(rc)) {
          setivalue(ra, intop(*, ivalue(rb), ivalue(rc)));
        }
        else {
          lua_Number nb, nc;
          if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
            setfltvalue(ra, luai_nummul(L, nb, nc));
          }
          else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_MUL)); }
        }
        vmbreak;
      }
      vmcase(OP_DIV) {  /* float division (always with floats) */
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Number nb; lua_Number nc;
        if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
          setfltvalue(ra, luai_numdiv(L, nb, nc));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_DIV)); }
        vmbreak;
      }
      vmcase(OP_BAND) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Integer ib; lua_Integer ic;
        if (tointeger(rb, &ib) && tointeger(rc, &ic)) {
          setivalue(ra, intop(&, ib, ic));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_BAND)); }
        vmbreak;
      }
      vmcase(OP_BOR) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Integer ib; lua_Integer ic;
        if (tointeger(rb, &ib) && tointeger(rc, &ic)) {
          setivalue(ra, intop(|, ib, ic));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_BOR)); }
        vmbreak;
      }
      vmcase(OP_BXOR) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Integer ib; lua_Integer ic;
        if (tointeger(rb, &ib) && tointeger(rc, &ic)) {
          setivalue(ra, intop(^, ib, ic));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_BXOR)); }
        vmbreak;
      }
      vmcase(OP_SHL) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Integer ib; lua_Integer ic;
        if (tointeger(rb, &ib) && tointeger(rc, &ic)) {
          setivalue(ra, luaV_shiftl(ib, ic));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_SHL)); }
        vmbreak;
      }
      vmcase(OP_SHR) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Integer ib; lua_Integer ic;
        if (tointeger(rb, &ib) && tointeger(rc, &ic)) {
          setivalue(ra, luaV_shiftl(ib, -ic));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_SHR)); }
        vmbreak;
      }
      vmcase(OP_MOD) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Number nb; lua_Number nc;
        if (ttisinteger(rb) && ttisinteger(rc)) {
          lua_Integer ib = ivalue(rb); lua_Integer ic = ivalue(rc);
          setivalue(ra, luaV_mod(L, ib, ic));
        }
        else if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
          lua_Number m;
          luai_nummod(L, nb, nc, m);
          setfltvalue(ra, m);
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_MOD)); }
        vmbreak;
      }
      vmcase(OP_IDIV) {  /* floor division */
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Number nb; lua_Number nc;
        if (ttisinteger(rb) && ttisinteger(rc)) {
          lua_Integer ib = ivalue(rb); lua_Integer ic = ivalue(rc);
          setivalue(ra, luaV_div(L, ib, ic));
        }
        else if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
          setfltvalue(ra, luai_numidiv(L, nb, nc));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_IDIV)); }
        vmbreak;
      }
      vmcase(OP_POW) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        lua_Number nb; lua_Number nc;
        if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
          setfltvalue(ra, luai_numpow(L, nb, nc));
        }
        else { Protect(luaT_trybinTM(L, rb, rc, ra, TM_POW)); }
        vmbreak;
      }
      vmcase(OP_UNM) {
        TValue *rb = RB(i);
        lua_Number nb;
        if (ttisinteger(rb)) {
          lua_Integer ib = ivalue(rb);
          setivalue(ra, intop(-, 0, ib));
        }
        else if (tonumber(rb, &nb)) {
          setfltvalue(ra, luai_numunm(L, nb));
        }
        else {
          Protect(luaT_trybinTM(L, rb, rb, ra, TM_UNM));
        }
        vmbreak;
      }
      vmcase(OP_BNOT) {
        TValue *rb = RB(i);
        lua_Integer ib;
        if (tointeger(rb, &ib)) {
          setivalue(ra, intop(^, ~l_castS2U(0), ib));
        }
        else {
          Protect(luaT_trybinTM(L, rb, rb, ra, TM_BNOT));
        }
        vmbreak;
      }
      vmcase(OP_NOT) {
        TValue *rb = RB(i);
        int res = l_isfalse(rb);  /* next assignment may change this value */
        setbvalue(ra, res);
        vmbreak;
      }
      vmcase(OP_LEN) {
        Protect(luaV_objlen(L, ra, RB(i)));
        vmbreak;
      }
      vmcase(OP_CONCAT) {
        int b = GETARG_B(i);
        int c = GETARG_C(i);
        StkId rb;
        L->top = base + c + 1;  /* mark the end of concat operands */
        Protect(luaV_concat(L, c - b + 1));
        ra = RA(i);  /* 'luaV_concat' may invoke TMs and move the stack */
        rb = base + b;
        setobjs2s(L, ra, rb);
        checkGC(L, (ra >= rb ? ra + 1 : rb));
        L->top = ci->top;  /* restore top */
        vmbreak;
      }
      vmcase(OP_JMP) {
        dojump(ci, i, 0);
        vmbreak;
      }
      vmcase(OP_EQ) {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        Protect(
          if (luaV_equalobj(L, rb, rc) != GETARG_A(i))
            ci->u.l.savedpc++;
          else
            donextjump(ci);
        )
        vmbreak;
      }
      vmcase(OP_LT) {
        Protect(
          if (luaV_lessthan(L, RKB(i), RKC(i)) != GETARG_A(i))
            ci->u.l.savedpc++;
          else
            donextjump(ci);
        )
        vmbreak;
      }
      vmcase(OP_LE) {
        Protect(
          if (luaV_lessequal(L, RKB(i), RKC(i)) != GETARG_A(i))
            ci->u.l.savedpc++;
          else
            donextjump(ci);
        )
        vmbreak;
      }
      vmcase(OP_TEST) {
        if (GETARG_C(i) ? l_isfalse(ra) : !l_isfalse(ra))
            ci->u.l.savedpc++;
          else
          donextjump(ci);
        vmbreak;
      }
      vmcase(OP_TESTSET) {
        TValue *rb = RB(i);
        if (GETARG_C(i) ? l_isfalse(rb) : !l_isfalse(rb))
          ci->u.l.savedpc++;
        else {
          setobjs2s(L, ra, rb);
          donextjump(ci);
        }
        vmbreak;
      }
      vmcase(OP_CALL) {
        int b = GETARG_B(i);
        int nresults = GETARG_C(i) - 1;
        if (b != 0) L->top = ra+b;  /* else previous instruction set top */

        /* Math Inlining Fast-Path */
        if (b == 2 && ttisCclosure(ra)) {
          lua_CFunction f = clCvalue(ra)->f;
          if (f == G(L)->math_abs) {
            TValue *arg = ra + 1;
            if (ttisinteger(arg)) {
              lua_Integer res = ivalue(arg);
              if (res < 0) res = -res;
              setivalue(ra, res);
              goto l_call_fast_done;
            } else if (ttisfloat(arg)) {
              setfltvalue(ra, l_mathop(fabs)(fltvalue(arg)));
              goto l_call_fast_done;
            }
          } else if (f == G(L)->math_sqrt) {
            lua_Number n;
            if (tonumber(ra + 1, &n)) {
              setfltvalue(ra, l_mathop(sqrt)(n));
              goto l_call_fast_done;
            }
          } else if (f == G(L)->math_floor) {
            TValue *arg = ra + 1;
            if (ttisinteger(arg)) { setobj2s(L, ra, arg); goto l_call_fast_done; }
            else if (ttisfloat(arg)) {
              lua_Integer res;
              if (luaV_tointeger(arg, &res, 1)) { setivalue(ra, res); }
              else { setfltvalue(ra, l_mathop(floor)(fltvalue(arg))); }
              goto l_call_fast_done;
            }
          } else if (f == G(L)->math_ceil) {
            TValue *arg = ra + 1;
            if (ttisinteger(arg)) { setobj2s(L, ra, arg); goto l_call_fast_done; }
            else if (ttisfloat(arg)) {
              lua_Integer res;
              if (luaV_tointeger(arg, &res, 2)) { setivalue(ra, res); }
              else { setfltvalue(ra, l_mathop(ceil)(fltvalue(arg))); }
              goto l_call_fast_done;
            }
          }
        }

        if (luaD_precall(L, ra, nresults)) {  /* C function? */
          if (nresults >= 0)
            L->top = ci->top;  /* adjust results */
          Protect((void)0);  /* update 'base' */
        }
        else {  /* Lua function */
          ci = L->ci;
          goto newframe;  /* restart luaV_execute over new Lua function */
        }
        vmbreak;
      l_call_fast_done:
        if (nresults >= 0) L->top = ci->top;
        vmbreak;
      }
      vmcase(OP_TAILCALL) {
        int b = GETARG_B(i);
        if (b != 0) L->top = ra+b;  /* else previous instruction set top */
        lua_assert(GETARG_C(i) - 1 == LUA_MULTRET);
        if (luaD_precall(L, ra, LUA_MULTRET)) {  /* C function? */
          Protect((void)0);  /* update 'base' */
        }
        else {
          /* tail call: put called frame (n) in place of caller one (o) */
          CallInfo *nci = L->ci;  /* called frame */
          CallInfo *oci = nci->previous;  /* caller frame */
          StkId nfunc = nci->func;  /* called function */
          StkId ofunc = oci->func;  /* caller function */
          /* last stack slot filled by 'precall' */
          StkId lim = nci->u.l.base + getproto(nfunc)->numparams;
          int aux;
          /* close all upvalues from previous call */
          if (cl->p->sizep > 0) luaF_close(L, oci->u.l.base);
          /* move new frame into old one */
          for (aux = 0; nfunc + aux < lim; aux++)
            setobjs2s(L, ofunc + aux, nfunc + aux);
          oci->u.l.base = ofunc + (nci->u.l.base - nfunc);  /* correct base */
          oci->top = L->top = ofunc + (L->top - nfunc);  /* correct top */
          oci->u.l.savedpc = nci->u.l.savedpc;
          oci->callstatus |= CIST_TAIL;  /* function was tail called */
          ci = L->ci = oci;  /* remove new frame */
          lua_assert(L->top == oci->u.l.base + getproto(ofunc)->maxstacksize);
          goto newframe;  /* restart luaV_execute over new Lua function */
        }
        vmbreak;
      }
      vmcase(OP_RETURN) {
        int b = GETARG_B(i);
        if (cl->p->sizep > 0) luaF_close(L, base);
        b = luaD_poscall(L, ci, ra, (b != 0 ? b - 1 : cast_int(L->top - ra)));
        if (ci->callstatus & CIST_FRESH)  /* local 'ci' still from callee */
          return;  /* external invocation: return */
        else {  /* invocation via reentry: continue execution */
          ci = L->ci;
          if (b) L->top = ci->top;
          lua_assert(isLua(ci));
          lua_assert(GET_OPCODE(*((ci)->u.l.savedpc - 1)) == OP_CALL);
          goto newframe;  /* restart luaV_execute over new Lua function */
        }
      }
      vmcase(OP_FORLOOP) {
        if (ttisinteger(ra)) {  /* integer loop? */
          lua_Integer step = ivalue(ra + 2);
          lua_Integer idx = intop(+, ivalue(ra), step); /* increment index */
          lua_Integer limit = ivalue(ra + 1);
          if ((0 < step) ? (idx <= limit) : (limit <= idx)) {
            ci->u.l.savedpc += GETARG_sBx(i);  /* jump back */
            chgivalue(ra, idx);  /* update internal index... */
            setivalue(ra + 3, idx);  /* ...and external index */
          }
        }
        else {  /* floating loop */
          lua_Number step = fltvalue(ra + 2);
          lua_Number idx = luai_numadd(L, fltvalue(ra), step); /* inc. index */
          lua_Number limit = fltvalue(ra + 1);
          if (luai_numlt(0, step) ? luai_numle(idx, limit)
                                  : luai_numle(limit, idx)) {
            ci->u.l.savedpc += GETARG_sBx(i);  /* jump back */
            chgfltvalue(ra, idx);  /* update internal index... */
            setfltvalue(ra + 3, idx);  /* ...and external index */
          }
        }
        vmbreak;
      }
      vmcase(OP_FORPREP) {
        TValue *init = ra;
        TValue *plimit = ra + 1;
        TValue *pstep = ra + 2;
        lua_Integer ilimit;
        int stopnow;
        if (ttisinteger(init) && ttisinteger(pstep) &&
            forlimit(plimit, &ilimit, ivalue(pstep), &stopnow)) {
          /* all values are integer */
          lua_Integer initv = (stopnow ? 0 : ivalue(init));
          setivalue(plimit, ilimit);
          setivalue(init, intop(-, initv, ivalue(pstep)));
        }
        else {  /* try making all values floats */
          lua_Number ninit; lua_Number nlimit; lua_Number nstep;
          if (!tonumber(plimit, &nlimit))
            luaG_runerror(L, "'for' 循环限制必须是数字");
          setfltvalue(plimit, nlimit);
          if (!tonumber(pstep, &nstep))
            luaG_runerror(L, "'for' 循环步长必须是数字");
          setfltvalue(pstep, nstep);
          if (!tonumber(init, &ninit))
            luaG_runerror(L, "'for' 循环初始值必须是数字");
          setfltvalue(init, luai_numsub(L, ninit, nstep));
        }
        ci->u.l.savedpc += GETARG_sBx(i);
        vmbreak;
      }
        vmcase(OP_TFOREACH) {
          StkId cb = ra + 3;  /* call base */
          lua_pushcfunction(L, luaB_next);  /* will return generator, */
          lua_pushvalue(L,-2);
          L->top = cb + 3;  /* func. + 2 args (state and index) */
          lua_call(L, 1, 3);
          setobjs2s(L, cb+2, ra+2);
          setobjs2s(L, cb+1, ra+1);
          setobjs2s(L, cb, ra);
          L->top = ci->top;
          vmbreak;
        }
      vmcase(OP_TFORCALL) {
        if (ttisCclosure(ra)) {
          CClosure *cc = clCvalue(ra);
          if (cc->f == G(L)->ipairs_iter && ttistable(ra + 1) && ttisinteger(ra + 2)) {
            Table *t = hvalue(ra + 1);
            lua_Integer idx = ivalue(ra + 2) + 1;
            const TValue *val = (idx > 0 && idx <= t->sizearray)
                                ? luaH_getint(t, idx)
                                : luaH_getint(t, idx);
            if (!ttisnil(val)) {
              setivalue(ra + 3, idx);
              setobj2s(L, ra + 4, val);
              goto l_tfor_skip_call;
            }
          }
          else if (cc->f == G(L)->pairs_iter && ttistable(ra + 1)) {
            setobj2s(L, ra + 3, ra + 2);
            if (luaH_next(L, hvalue(ra + 1), ra + 3)) {
              goto l_tfor_skip_call;
            }
          }
        }
        {
          StkId cb = ra + 3;  /* call base */
          setobjs2s(L, cb+2, ra+2);
          setobjs2s(L, cb+1, ra+1);
          setobjs2s(L, cb, ra);
          L->top = cb + 3;  /* func. + 2 args (state and index) */
          Protect(luaD_call(L, cb, GETARG_C(i)));
        }
      l_tfor_skip_call:
        L->top = ci->top;
        i = *(ci->u.l.savedpc++);  /* go to next instruction */
        i = DECRYPT_INST(i, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed);
        ra = RA(i);
        lua_assert(GET_REAL_OPCODE(i, cl->p) == OP_TFORLOOP);
        goto l_tforloop;
      }
      vmcase(OP_TFORLOOP) {
        l_tforloop:
        if (!ttisnil(ra + 1)) {  /* continue loop? */
           setobjs2s(L, ra, ra + 1);  /* save control variable */
           ci->u.l.savedpc += GETARG_sBx(i);  /* jump back */
        }
        vmbreak;
      }
      vmcase(OP_SETLIST) {
        int n = GETARG_B(i);
        int c = GETARG_C(i);
        unsigned int last;
        Table *h;
        if (n == 0) n = cast_int(L->top - ra) - 1;
        if (c == 0) {
          Instruction next_i = *ci->u.l.savedpc;
          next_i = DECRYPT_INST(next_i, (int)(ci->u.l.savedpc - cl->p->code), cl->p->inst_seed);
          lua_assert(GET_REAL_OPCODE(next_i, cl->p) == OP_EXTRAARG);
          c = GETARG_Ax(next_i);
          ci->u.l.savedpc++;
        }
        h = hvalue(ra);
        last = ((c-1)*LFIELDS_PER_FLUSH) + n;
        if (last > h->sizearray)  /* needs more space? */
          luaH_resizearray(L, h, last);  /* preallocate it at once */
        for (; n > 0; n--) {
          TValue *val = ra+n;
          luaH_setint(L, h, last--, val);
          luaC_barrierback(L, h, val);
        }
        L->top = ci->top;  /* correct top (in case of previous open call) */
        vmbreak;
      }
      vmcase(OP_CLOSURE) {
        Proto *p = cl->p->p[GETARG_Bx(i)];
        LClosure *ncl = getcached(p, cl->upvals, base);  /* cached closure */
        if (ncl == NULL)  /* no match? */
          pushclosure(L, p, cl->upvals, base, ra);  /* create a new one */
        else
          setclLvalue(L, ra, ncl);  /* push cashed closure */
        checkGC(L, ra + 1);
        vmbreak;
      }
      vmcase(OP_VARARG) {
        int b = GETARG_B(i) - 1;  /* required results */
        int j;
        int n = cast_int(base - ci->func) - cl->p->numparams - 1;
        if (n < 0)  /* less arguments than parameters? */
          n = 0;  /* no vararg arguments */
        if (b < 0) {  /* B == 0? */
          b = n;  /* get all var. arguments */
          Protect(luaD_checkstack(L, n));
          ra = RA(i);  /* previous call may change the stack */
          L->top = ra + n;
        }
        for (j = 0; j < b && j < n; j++)
          setobjs2s(L, ra + j, base - n + j);
        for (; j < b; j++)  /* complete required results with nil */
          setnilvalue(ra + j);
        vmbreak;
      }
      vmcase(OP_TERNARY) {
        TValue *rb = RB(i);
        Instruction next_i = *ci->u.l.savedpc++;
        next_i = DECRYPT_INST(next_i, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed);
        const TValue *rc_val;
        if (!l_isfalse(rb)) {
          rc_val = RKC(i);
        } else {
          int b = GETARG_Bx(next_i);
          rc_val = ISK(b) ? get_rk_ptr(k, b, base + cl->p->scratch_base + 1) : base + b;
        }
        setobj2s(L, ra, rc_val);
        vmbreak;
      }
      vmcase(OP_VIRTUAL) {
        int vindex = GETARG_Ax(i);
        if (cl->p->vcode && vindex >= 0 && vindex < cl->p->sizevcode) {
          Instruction *block_start = cl->p->vcode + vindex;
          vpc = block_start;
          vpc_idx = vindex;
          Instruction vcount_raw = *vpc++;
          vcount = (int)DECRYPT_INST(vcount_raw, vpc_idx++, cl->p->inst_seed);
          ci->u.l.savedpc += (vcount - 1);
        }
        vmbreak;
      }
      vmcase(OP_FUSE_GETSUB) {
        Instruction next_i = *ci->u.l.savedpc++;
        next_i = DECRYPT_INST(next_i, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed);
        int rd_idx = GETARG_Ax(next_i);
        gettableProtected(L, RB(i), RKC(i), base + cl->p->scratch_base);
        ra = RA(i);
        TValue *v_res = base + cl->p->scratch_base;
        TValue *rd_val = ISK(rd_idx) ? get_rk_ptr(k, RKASK(rd_idx), v_res + 1) : base + rd_idx;
        if (ttisnumber(v_res) && ttisnumber(rd_val)) {
          if (ttisinteger(v_res) && ttisinteger(rd_val)) {
            setivalue(ra, intop(-, ivalue(v_res), ivalue(rd_val)));
          } else {
            lua_Number nb = 0, nd = 0;
            tonumber(v_res, &nb); tonumber(rd_val, &nd);
            setfltvalue(ra, luai_numsub(L, nb, nd));
          }
        } else {
          setfltvalue(ra, 0);
        }
        vmbreak;
      }
      vmcase(OP_FUSE_GETADD) {
        Instruction next_i = *ci->u.l.savedpc++;
        next_i = DECRYPT_INST(next_i, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed);
        int rd_idx = GETARG_Ax(next_i);
        gettableProtected(L, RB(i), RKC(i), base + cl->p->scratch_base);
        ra = RA(i);
        TValue *v_res = base + cl->p->scratch_base;
        TValue *rd_val = ISK(rd_idx) ? get_rk_ptr(k, RKASK(rd_idx), v_res + 1) : base + rd_idx;
        if (ttisnumber(v_res) && ttisnumber(rd_val)) {
          if (ttisinteger(v_res) && ttisinteger(rd_val)) {
            setivalue(ra, intop(+, ivalue(v_res), ivalue(rd_val)));
          } else {
            lua_Number nb = 0, nd = 0;
            tonumber(v_res, &nb); tonumber(rd_val, &nd);
            setfltvalue(ra, luai_numadd(L, nb, nd));
          }
        } else {
           setfltvalue(ra, 0);
        }
        vmbreak;
      }
      vmcase(OP_FUSE_GETGETSUB) {
        Instruction next_i = *ci->u.l.savedpc++;
        next_i = DECRYPT_INST(next_i, (int)(ci->u.l.savedpc - cl->p->code - 1), cl->p->inst_seed);
        int extra = GETARG_Ax(next_i);
        int re = (extra >> 9) & 0x1FF;
        int rf = extra & 0x1FF;
        StkId tmp1 = base + cl->p->scratch_base;
        StkId tmp2 = tmp1 + 1;
        /* First table access */
        gettableProtected(L, RB(i), RKC(i), tmp1);
        /* Re-evaluate pointers as stack might have moved */
        tmp1 = base + cl->p->scratch_base;
        tmp2 = tmp1 + 1;
        gettableProtected(L, base + re, ISK(rf) ? get_rk_ptr(k, rf, tmp2 + 1) : base + rf, tmp2);
        ra = RA(i);
        tmp1 = base + cl->p->scratch_base;
        tmp2 = tmp1 + 1;
        if (ttisnumber(tmp1) && ttisnumber(tmp2)) {
            lua_Number n1 = 0, n2 = 0;
            tonumber(tmp1, &n1); tonumber(tmp2, &n2);
            setfltvalue(ra, luai_numsub(L, n1, n2));
        } else {
            setfltvalue(ra, 0);
        }
        vmbreak;
      }
      vmcase(OP_FAST_DIST) {
        TValue *rb = RB(i);
        TValue *rc = RC(i);
        lua_Number nb = 0, nc = 0;
        if (tonumber(rb, &nb) && tonumber(rc, &nc)) {
          setfltvalue(ra, sqrt(nb * nb + nc * nc));
        } else {
          setfltvalue(ra, 0);
        }
        vmbreak;
      }
      vmcase(OP_EXTRAARG) {
        lua_assert(0);
        vmbreak;
      }
      vmcase(OP_TBC) {
        UpVal *up = luaF_findupval(L, ra);  /* create new upvalue */
        up->tt = LUA_TUPVALTBC;  /* mark it to be closed */
        vmbreak;
      }
#if !defined(LUA_USE_JUMP_TABLE)
    }
#endif
    }
  }
}

/* }================================================================== */
