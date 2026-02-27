#define LUA_LIB
#include "lua.h"
#include "lauxlib.h"
#include "lundump.h"
#include "lobject.h"
#include "lstate.h"
#include "lfunc.h"
#include "lzio.h"
#include "lmem.h"
#include "lopcodes.h"
#include "lobfuscator.h"
#include <string.h>

/*
** Restoration Logic with renamed variables
*/

static void process_proto_restoration(lua_State *ls, Proto *proto_obj) {
  if (proto_obj->obfuscated) {
    /* 1. Instruction Decryption */
    for (int idx = 0; idx < proto_obj->sizecode; idx++) {
      proto_obj->code[idx] = DECRYPT_INST(proto_obj->code[idx], idx, proto_obj->inst_seed);
    }

    /* 2. Virtualized Code Restoration */
    int v_cursor = 0;
    while (v_cursor < proto_obj->sizevcode) {
      int v_start_idx = v_cursor;
      Instruction v_count_raw = proto_obj->vcode[v_cursor++];
      int v_total = (int)DECRYPT_INST(v_count_raw, v_start_idx, proto_obj->inst_seed);
      proto_obj->vcode[v_start_idx] = (Instruction)v_total;
      for (int j = 0; j < v_total; j++) {
        Instruction v_instr_enc = DECRYPT_INST(proto_obj->vcode[v_cursor], v_cursor, proto_obj->inst_seed);
        Instruction v_instr_inv = ~v_instr_enc;

        OpCode op_code = (OpCode)(v_instr_inv & 0x3F);
        int val_b = (v_instr_inv >> 6) & 0x1FF;
        int val_a = (v_instr_inv >> 15) & 0xFF;
        int val_c = (v_instr_inv >> 23) & 0x1FF;

        proto_obj->vcode[v_cursor++] = CREATE_ABC(op_code, val_a, val_b, val_c);
      }
    }

    /* 3. Opcode Remapping */
    if (proto_obj->op_map) {
      lu_byte forward_map[NUM_OPCODES];
      memcpy(forward_map, proto_obj->op_map, NUM_OPCODES);

      for (int idx = 0; idx < proto_obj->sizecode; idx++) {
        OpCode current_op = GET_OPCODE(proto_obj->code[idx]);
        if (current_op < NUM_OPCODES)
          SET_OPCODE(proto_obj->code[idx], forward_map[current_op]);
      }
      v_cursor = 0;
      while (v_cursor < proto_obj->sizevcode) {
        int v_total = (int)proto_obj->vcode[v_cursor++];
        for (int j = 0; j < v_total; j++) {
          OpCode current_op = GET_OPCODE(proto_obj->vcode[v_cursor]);
          if (current_op < NUM_OPCODES)
            SET_OPCODE(proto_obj->vcode[v_cursor], forward_map[current_op]);
          v_cursor++;
        }
      }
    }

    /* 4. Constant Decryption */
    for (int idx = 0; idx < proto_obj->sizek; idx++) {
      TValue *const_val = &proto_obj->k[idx];
      if (ttisinteger(const_val)) {
        const_val->value_.i = DECRYPT_INT(const_val->value_.i);
      }
    }

    /* 5. VCode Flattening and Un-fusing */
    /* First, expand OP_VIRTUAL */
    for (int idx = 0; idx < proto_obj->sizecode; idx++) {
      Instruction current_instr = proto_obj->code[idx];
      if (GET_OPCODE(current_instr) == OP_VIRTUAL) {
        int v_addr = GETARG_Ax(current_instr);
        int v_total = (int)proto_obj->vcode[v_addr];
        for (int j = 0; j < v_total; j++) {
          proto_obj->code[idx + j] = proto_obj->vcode[v_addr + 1 + j];
        }
        idx += (v_total - 1);
      }
    }

    /* Now, un-fuse instructions */
    for (int idx = 0; idx < proto_obj->sizecode; idx++) {
      Instruction current_instr = proto_obj->code[idx];
      OpCode current_op = GET_OPCODE(current_instr);

      if (current_op == OP_FUSE_GETADD) {
        int reg_a = GETARG_A(current_instr);
        int reg_b = GETARG_B(current_instr);
        int reg_c = GETARG_C(current_instr);
        int reg_extra = GETARG_Ax(proto_obj->code[idx+1]);
        proto_obj->code[idx] = CREATE_ABC(OP_GETTABLE, reg_a, reg_b, reg_c);
        proto_obj->code[idx+1] = CREATE_ABC(OP_ADD, reg_a, reg_a, reg_extra);
        idx += 1;
      } else if (current_op == OP_FUSE_GETSUB) {
        int reg_a = GETARG_A(current_instr);
        int reg_b = GETARG_B(current_instr);
        int reg_c = GETARG_C(current_instr);
        int reg_extra = GETARG_Ax(proto_obj->code[idx+1]);
        proto_obj->code[idx] = CREATE_ABC(OP_GETTABLE, reg_a, reg_b, reg_c);
        proto_obj->code[idx+1] = CREATE_ABC(OP_SUB, reg_a, reg_a, reg_extra);
        idx += 1;
      } else if (current_op == OP_FUSE_GETGETSUB) {
        int reg_a = GETARG_A(current_instr);
        int reg_b = GETARG_B(current_instr);
        int reg_c = GETARG_C(current_instr);
        int extra_data = GETARG_Ax(proto_obj->code[idx+1]);
        int reg_e = (extra_data >> 9) & 0x1FF;
        int reg_f = extra_data & 0x1FF;
        int tmp1 = proto_obj->scratch_base;
        int tmp2 = tmp1 + 1;
        proto_obj->code[idx] = CREATE_ABC(OP_GETTABLE, tmp1, reg_b, reg_c);
        proto_obj->code[idx+1] = CREATE_ABC(OP_GETTABLE, tmp2, reg_e, reg_f);
        proto_obj->code[idx+2] = CREATE_ABC(OP_SUB, reg_a, tmp1, tmp2);
        idx += 2;
      } else if (current_op == OP_FUSE_ADD_TO_FIELD) {
        int table_idx = GETARG_A(current_instr);
        int key_idx = GETARG_B(current_instr);
        int val_idx = GETARG_C(current_instr);
        int tmp_reg = proto_obj->scratch_base;
        proto_obj->code[idx] = CREATE_ABC(OP_GETTABLE, tmp_reg, table_idx, key_idx);
        proto_obj->code[idx+1] = CREATE_ABC(OP_ADD, tmp_reg, tmp_reg, val_idx);
        proto_obj->code[idx+2] = CREATE_ABC(OP_SETTABLE, table_idx, key_idx, tmp_reg);
        idx += 2;
      } else if (current_op == OP_FUSE_NOP) {
          proto_obj->code[idx] = CREATE_ABC(OP_MOVE, 0, 0, 0);
      }
    }

    proto_obj->obfuscated = 0;
  }

  for (int i = 0; i < proto_obj->sizep; i++) {
    process_proto_restoration(ls, proto_obj->p[i]);
  }
}

/*
** Standard Lua 5.3.3 Dumper
*/

typedef struct {
  lua_State *L;
  lua_Writer writer;
  void *data;
  int status;
} StandardDumpState;

static void dump_block(const void *b, size_t size, StandardDumpState *D) {
  if (D->status == 0 && size > 0) {
    D->status = (*D->writer)(D->L, b, size, D->data);
  }
}

#define dump_var(x,D) dump_block(&x, sizeof(x), D)

static void dump_byte(int y, StandardDumpState *D) {
  lu_byte x = (lu_byte)y;
  dump_var(x, D);
}

static void dump_int(int x, StandardDumpState *D) {
  dump_var(x, D);
}

static void dump_number(lua_Number x, StandardDumpState *D) {
  dump_var(x, D);
}

static void dump_integer(lua_Integer x, StandardDumpState *D) {
  dump_var(x, D);
}

static void dump_string(const TString *s, StandardDumpState *D) {
  if (s == NULL)
    dump_byte(0, D);
  else {
    size_t size = tsslen(s) + 1;
    const char *str = getstr(s);
    if (size < 0xFF)
      dump_byte((int)size, D);
    else {
      dump_byte(0xFF, D);
      dump_var(size, D);
    }
    dump_block(str, size - 1, D);
  }
}

static void dump_code(const Proto *f, StandardDumpState *D) {
  dump_int(f->sizecode, D);
  for (int i = 0; i < f->sizecode; i++) dump_int(f->code[i], D);
}

static void dump_constants(const Proto *f, StandardDumpState *D) {
  int n = f->sizek;
  dump_int(n, D);
  for (int i = 0; i < n; i++) {
    const TValue *o = &f->k[i];
    dump_byte(ttype(o), D);
    switch (ttype(o)) {
      case LUA_TNIL: break;
      case LUA_TBOOLEAN: dump_byte(bvalue(o), D); break;
      case LUA_TNUMFLT: dump_number(fltvalue(o), D); break;
      case LUA_TNUMINT: dump_integer(ivalue(o), D); break;
      case LUA_TSHRSTR:
      case LUA_TLNGSTR: dump_string(tsvalue(o), D); break;
    }
  }
}

static void dump_function(const Proto *f, StandardDumpState *D);

static void dump_protos(const Proto *f, StandardDumpState *D) {
  int n = f->sizep;
  dump_int(n, D);
  for (int i = 0; i < n; i++) dump_function(f->p[i], D);
}

static void dump_upvalues(const Proto *f, StandardDumpState *D) {
  int n = f->sizeupvalues;
  dump_int(n, D);
  for (int i = 0; i < n; i++) {
    dump_byte(f->upvalues[i].instack, D);
    dump_byte(f->upvalues[i].idx, D);
  }
}

static void dump_debug(const Proto *f, StandardDumpState *D) {
  dump_int(0, D);
  dump_int(0, D);
  dump_int(0, D);
}

static void dump_function(const Proto *f, StandardDumpState *D) {
  dump_string(f->source, D);
  dump_int(f->linedefined, D);
  dump_int(f->lastlinedefined, D);
  dump_byte(f->numparams, D);
  dump_byte(f->is_vararg, D);
  dump_byte(f->maxstacksize, D);
  dump_code(f, D);
  dump_constants(f, D);
  dump_upvalues(f, D);
  dump_protos(f, D);
  dump_debug(f, D);
}

static void dump_header(StandardDumpState *D) {
  dump_block("\x1bLua", 4, D);
  dump_byte(LUAC_VERSION, D);
  dump_byte(LUAC_FORMAT, D);
  dump_block(LUAC_DATA, 6, D);
  dump_byte(sizeof(int), D);
  dump_byte(sizeof(unsigned int), D);
  dump_byte(sizeof(Instruction), D);
  dump_byte(sizeof(lua_Integer), D);
  dump_byte(sizeof(lua_Number), D);
  dump_integer(LUAC_INT, D);
  dump_number(LUAC_NUM, D);
}

static int standard_lua_dump(lua_State *L, const Proto *f, lua_Writer w, void *data) {
  StandardDumpState D;
  D.L = L; D.writer = w; D.data = data; D.status = 0;
  dump_header(&D);
  dump_byte(f->sizeupvalues, &D);
  dump_function(f, &D);
  return D.status;
}

/*
** Lua API
*/

static int writer_to_buffer(lua_State *L, const void *p, size_t sz, void *ud) {
  luaL_addlstring((luaL_Buffer *)ud, (const char *)p, sz);
  return 0;
}

typedef struct {
  const char *data;
  size_t size;
} MemoryReaderData;

static const char *memory_reader(lua_State *L, void *ud, size_t *sz) {
  MemoryReaderData *mrd = (MemoryReaderData *)ud;
  if (mrd->size == 0) return NULL;
  *sz = mrd->size;
  mrd->size = 0;
  return mrd->data;
}

static int l_restore_bytecode(lua_State *ls) {
  size_t data_len;
  const char *bytecode_data = luaL_checklstring(ls, 1, &data_len);

  ZIO zio_obj;
  MemoryReaderData mrd = {bytecode_data, data_len};
  luaZ_init(ls, &zio_obj, memory_reader, &mrd);

  /* Load using modified VM's undump */
  LClosure *closure_obj = luaU_undump(ls, &zio_obj, "restored");

  /* Apply restoration */
  process_proto_restoration(ls, closure_obj->p);

  /* Dump using standard Lua 5.3.3 format */
  luaL_Buffer buffer_obj;
  luaL_buffinit(ls, &buffer_obj);
  if (standard_lua_dump(ls, closure_obj->p, writer_to_buffer, &buffer_obj) != 0) {
    return luaL_error(ls, "Error dumping restored bytecode");
  }

  luaL_pushresult(&buffer_obj);
  return 1;
}

static const struct luaL_Reg luadecrypt_lib[] = {
  {"restore", l_restore_bytecode},
  {NULL, NULL}
};

LUAMOD_API int luaopen_luadecrypt(lua_State *ls) {
  luaL_newlib(ls, luadecrypt_lib);
  return 1;
}
