#define ldump_c
#define LUA_CORE

#include "lprefix.h"
#include <stddef.h>
#include "lua.h"
#include "lobfuscator.h"
#include "lopcodes.h"
#include "lobject.h"
#include "lstate.h"
#include "lundump.h"
#include "lsha256.h"

typedef struct {
    lua_State *L;
    lua_Writer writer;
    void *data;
    int strip;
    int status;
    SHA256_CTX sha256_ctx;
} DumpState;

#define DumpVector(v,n,D)	DumpBlock(v,(n)*sizeof((v)[0]),D)
#define DumpLiteral(s,D)	DumpBlock(s, sizeof(s) - sizeof(char), D)

static void DumpBlock (const void *b, size_t size, DumpState *D) {
  if (D->status == 0 && size > 0) {
    l_sha256_update(&D->sha256_ctx, (const uint8_t *)b, size);
    D->status = (*D->writer)(D->L, b, size, D->data);
  }
}

#define DumpVar(x,D)		DumpVector(&x,1,D)

static void DumpByte (int y, DumpState *D) {
  lu_byte x = (lu_byte)y;
  DumpVar(x, D);
}

static void DumpInt (int x, DumpState *D) {
  DumpVar(x, D);
}

static void DumpNumber (lua_Number x, DumpState *D) {
  DumpVar(x, D);
}

static void DumpInteger (lua_Integer x, DumpState *D) {
  DumpVar(x, D);
}

static void DumpString (const TString *s, DumpState *D) {
  if (s == NULL)
    DumpByte(0, D);
  else {
    unsigned int size = tsslen(s) + 1;
    const char *str = getstr(s);
    if (size < 0xFF)
      DumpByte(cast_int(size), D);
    else {
      DumpByte(0xFF, D);
      DumpVar(size, D);
    }
    for (size_t i = 0; i < size - 1; i++) {
        DumpByte((lu_byte)(str[i]), D);
    }
  }
}

static void DumpCode (const Proto *f, DumpState *D) {
  int i;
  DumpInt(f->sizecode, D);
  for (i = 0; i < f->sizecode; i++) DumpInt(f->code[i], D);
}

static void DumpVCode (const Proto *f, DumpState *D) {
  int i;
  DumpInt(f->sizevcode, D);
  for (i = 0; i < f->sizevcode; i++) DumpInt(f->vcode[i], D);
}

static void DumpOpMap (const Proto *f, DumpState *D) {
  if (f->op_map) {
    DumpByte(1, D);
    DumpVector(f->op_map, NUM_OPCODES, D);
  } else DumpByte(0, D);
}

static void DumpFunction(const Proto *f, TString *psource, DumpState *D);

static void DumpConstants (const Proto *f, DumpState *D) {
  int i, n = f->sizek;
  DumpInt(n, D);
  for (i = 0; i < n; i++) {
    const TValue *o = &f->k[i];
    DumpByte(ttype(o), D);
    switch (ttype(o)) {
      case LUA_TNIL: break;
      case LUA_TBOOLEAN: DumpByte(bvalue(o), D); break;
      case LUA_TNUMFLT: DumpNumber(fltvalue(o), D); break;
      case LUA_TNUMINT: DumpInteger(ivalue(o), D); break;
      case LUA_TSHRSTR:
      case LUA_TLNGSTR: DumpString(tsvalue(o), D); break;
      default: lua_assert(0);
    }
  }
}

static void DumpProtos (const Proto *f, DumpState *D) {
  int i, n = f->sizep;
  DumpInt(n, D);
  for (i = 0; i < n; i++) DumpFunction(f->p[i], f->source, D);
}

static void DumpUpvalues (const Proto *f, DumpState *D) {
  int i, n = f->sizeupvalues;
  DumpInt(n, D);
  for (i = 0; i < n; i++) {
    DumpByte(f->upvalues[i].instack, D);
    DumpByte(f->upvalues[i].idx, D);
  }
}

static void DumpDebug (const Proto *f, DumpState *D) {
  int n = 0;
  DumpInt(n, D);
  DumpInt(n, D);
  DumpInt(n, D);
}

static void DumpFunction (const Proto *f, TString *psource, DumpState *D) {
  //
  DumpString(NULL, D);
  DumpInt(0, D);
  DumpInt(0, D);
  DumpByte(f->numparams, D);
  DumpByte(f->is_vararg, D);
  DumpByte(f->maxstacksize, D);
  DumpByte(f->obfuscated, D);
  DumpInt(f->scratch_base, D);
  DumpInt(f->inst_seed, D);
  DumpOpMap(f, D);
  DumpCode(f, D);
  DumpVCode(f, D);
  DumpConstants(f, D);
  DumpUpvalues(f, D);
  DumpProtos(f, D);
  DumpDebug(f, D);
}

static void DumpHeader (DumpState *D) {
  DumpLiteral(LUA_SIGNATURE, D);
  DumpByte(LUAC_VERSION, D);
  DumpByte(LUAC_FORMAT, D);
  DumpLiteral(LUAC_DATA, D);
  DumpByte(sizeof(int), D);
  DumpByte(sizeof(unsigned int), D);
  DumpByte(sizeof(Instruction), D);
  DumpByte(sizeof(lua_Integer), D);
  DumpByte(sizeof(lua_Number), D);
  DumpInteger(LUAC_INT, D);
  DumpNumber(LUAC_NUM, D);
}

int luaU_dump(lua_State *L, const Proto *f, lua_Writer w, void *data, int strip) {
  DumpState D;
  D.L = L; D.writer = w; D.data = data; D.strip = strip; D.status = 0;
  l_sha256_init(&D.sha256_ctx);
  obfuscate_proto(L, (Proto *)f, 1);
  DumpHeader(&D);
  DumpByte(f->sizeupvalues, &D);
  DumpFunction(f, NULL, &D);
  if (D.status == 0) {
    uint8_t digest[32];
    l_sha256_final(&D.sha256_ctx, digest);
    DumpVector(digest, 32, &D);
  }
  return D.status;
}
