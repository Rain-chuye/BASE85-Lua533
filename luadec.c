#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "lua.h"
#include "lauxlib.h"

#define POS_OP 0
#define POS_A 6
#define POS_C 14
#define POS_B 23
#define GET_OPCODE(i) ((i) & 0x3F)
#define SET_OPCODE(i,o) ((i) = (((i) & ~0x3F) | ((uint32_t)(o) & 0x3F)))
#define GETARG_A(i) (((i) >> 6) & 0xFF)
#define GETARG_B(i) (((i) >> 23) & 0x1FF)
#define GETARG_C(i) (((i) >> 14) & 0x1FF)
#define GETARG_Ax(i) (((i) >> 6) & 0x3FFFFFF)
#define CREATE_ABC(o,a,b,c) ((uint32_t)(o) | ((uint32_t)(a) << 6) | ((uint32_t)(b) << 23) | ((uint32_t)(c) << 14))

static inline uint32_t decrypt_instruction(uint32_t i, int idx, uint32_t seed) {
    uint32_t k = seed ^ ((uint32_t)idx * 0x9E3779B9U);
    i -= k;
    i = (i >> 13) | (i << 19);
    i ^= k;
    return i;
}

#define LUA_INT_XOR 0xDEADBEEFCAFEBABEULL
#define LUA_INT_ADD 0x123456789ABCDEF0ULL
#define LUA_INT_MUL_INV 0xaaaaaaaaaaaaaaabULL
static inline int64_t decrypt_integer(int64_t i) {
    return (int64_t)((((uint64_t)i ^ LUA_INT_XOR) - LUA_INT_ADD) * LUA_INT_MUL_INV);
}

typedef enum {
    OP_MOVE, OP_LOADK, OP_LOADKX, OP_LOADBOOL, OP_LOADNIL, OP_GETUPVAL,
    OP_GETTABUP, OP_GETTABLE, OP_SETTABUP, OP_SETUPVAL, OP_SETTABLE,
    OP_NEWTABLE, OP_SELF, OP_ADD, OP_SUB, OP_MUL, OP_MOD, OP_POW,
    OP_DIV, OP_IDIV, OP_BAND, OP_BOR, OP_BXOR, OP_SHL, OP_SHR,
    OP_UNM, OP_BNOT, OP_NOT, OP_LEN, OP_CONCAT, OP_JMP, OP_EQ,
    OP_LT, OP_LE, OP_TEST, OP_TESTSET, OP_CALL, OP_TAILCALL,
    OP_RETURN, OP_FORLOOP, OP_FORPREP, OP_TFORCALL, OP_TFORLOOP,
    OP_SETLIST, OP_CLOSURE, OP_VARARG, OP_EXTRAARG,
    OP_TBC, OP_NEWARRAY, OP_TFOREACH, OP_TERNARY, OP_VIRTUAL,
    OP_FUSE_GETSUB, OP_FUSE_GETADD, OP_FUSE_GETGETSUB, OP_FAST_DIST,
    OP_FUSE_NOP, OP_FUSE_PARTICLE_DIST, OP_FUSE_ADD_TO_FIELD, OP_VARARGPREP
} OpCode;

typedef struct { uint8_t *data; size_t size; size_t cap; } Buffer;
static void buf_init(Buffer *b) { b->data = NULL; b->size = b->cap = 0; }
static void buf_free(Buffer *b) { free(b->data); }
static void buf_write(Buffer *b, const void *data, size_t len) {
    if (b->size + len > b->cap) {
        b->cap = (b->cap + len) * 2 + 1024;
        b->data = (uint8_t*)realloc(b->data, b->cap);
    }
    memcpy(b->data + b->size, data, len);
    b->size += len;
}
static void buf_write_byte(Buffer *b, uint8_t v) { buf_write(b, &v, 1); }
static void buf_write_int(Buffer *b, int v) { buf_write(b, &v, sizeof(int)); }
static void buf_write_uint32(Buffer *b, uint32_t v) { buf_write(b, &v, 4); }
static void buf_write_int64(Buffer *b, int64_t v) { buf_write(b, &v, 8); }
static void buf_write_double(Buffer *b, double v) { buf_write(b, &v, 8); }

typedef struct { const uint8_t *p; const uint8_t *end; } Reader;
static uint8_t r_byte(Reader *r) { return *r->p++; }
static int r_int(Reader *r) { int v; memcpy(&v, r->p, sizeof(int)); r->p += sizeof(int); return v; }
static uint32_t r_uint32(Reader *r) { uint32_t v; memcpy(&v, r->p, 4); r->p += 4; return v; }
static int64_t r_int64(Reader *r) { int64_t v; memcpy(&v, r->p, 8); r->p += 8; return v; }
static double r_double(Reader *r) { double v; memcpy(&v, r->p, 8); r->p += 8; return v; }
static const uint8_t* r_str(Reader *r, size_t *out_len) {
    uint8_t size = r_byte(r);
    if (size == 0xFF) {
        uint32_t s = r_uint32(r); *out_len = s;
        const uint8_t *ret = r->p; r->p += (s - 1); return ret;
    } else if (size == 0) {
        r_uint32(r); *out_len = 0; return NULL;
    } else {
        *out_len = size; const uint8_t *ret = r->p; r->p += (size - 1); return ret;
    }
}
static void w_str(Buffer *b, const uint8_t *s, size_t len) {
    if (len == 0) buf_write_byte(b, 0);
    else if (len < 0xFF) { buf_write_byte(b, (uint8_t)len); buf_write(b, s, len - 1); }
    else { buf_write_byte(b, 0xFF); buf_write_uint32(b, (uint32_t)len); buf_write(b, s, len - 1); }
}

static void process_proto(Reader *r, Buffer *b) {
    size_t slen; const uint8_t *source = r_str(r, &slen); w_str(b, source, slen);
    buf_write_int(b, r_int(r)); buf_write_int(b, r_int(r));
    buf_write_byte(b, r_byte(r)); buf_write_byte(b, r_byte(r)); buf_write_byte(b, r_byte(r));
    uint8_t obfuscated = r_byte(r); r_int(r); uint32_t seed = r_uint32(r);
    uint8_t inv_map[128]; memset(inv_map, 0, 128);
    if (r_byte(r)) {
        uint8_t op_map[128]; memcpy(op_map, r->p, 64); r->p += 64;
        for (int i = 0; i < 64; i++) inv_map[op_map[i]] = (uint8_t)i;
    }
    uint32_t sizecode = r_uint32(r);
    uint32_t *code = (uint32_t*)malloc(sizecode * 4); memcpy(code, r->p, sizecode * 4); r->p += sizecode * 4;
    uint32_t sizevcode = r_uint32(r);
    uint32_t *vcode = (uint32_t*)malloc(sizevcode * 4); memcpy(vcode, r->p, sizevcode * 4); r->p += sizevcode * 4;
    if (obfuscated) {
        for (uint32_t i = 0; i < sizecode; i++) code[i] = decrypt_instruction(code[i], (int)i, seed);
        for (uint32_t i = 0; i < sizecode; i++) {
            uint8_t op = (uint8_t)GET_OPCODE(code[i]);
            if (op == OP_VIRTUAL) {
                int vindex = GETARG_Ax(code[i]);
                int vptr = vindex;
                uint32_t vcount = decrypt_instruction(vcode[vptr++], vindex, seed);
                for (uint32_t j = 0; j < vcount; j++) {
                    uint32_t vi = ~decrypt_instruction(vcode[vptr++], vindex + 1 + (int)j, seed);
                    uint32_t dec_i = (vi & 0x3F) | (((vi >> 15) & 0xFF) << 6) | (((vi >> 6) & 0x1FF) << 23) | (((vi >> 23) & 0x1FF) << 14);
                    if (i + j < sizecode) code[i + j] = dec_i;
                }
            } else if (op == OP_FUSE_GETSUB && i + 1 < sizecode) {
                int ra = GETARG_A(code[i]), rb = GETARG_B(code[i]), rc = GETARG_C(code[i]), rd = GETARG_Ax(code[i+1]);
                code[i] = CREATE_ABC(OP_GETTABLE, ra, rb, rc); code[i+1] = CREATE_ABC(OP_SUB, ra, ra, rd); i++;
            } else if (op == OP_FUSE_GETADD && i + 1 < sizecode) {
                int ra = GETARG_A(code[i]), rb = GETARG_B(code[i]), rc = GETARG_C(code[i]), rd = GETARG_Ax(code[i+1]);
                code[i] = CREATE_ABC(OP_GETTABLE, ra, rb, rc); code[i+1] = CREATE_ABC(OP_ADD, ra, ra, rd); i++;
            } else if (op == OP_FUSE_NOP) code[i] = CREATE_ABC(OP_MOVE, 0, 0, 0);
        }
        for (uint32_t i = 0; i < sizecode; i++) SET_OPCODE(code[i], inv_map[GET_OPCODE(code[i])]);
    }
    buf_write_int(b, (int)sizecode); buf_write(b, code, sizecode * 4);
    free(code); free(vcode);
    uint32_t sizek = r_uint32(r); buf_write_int(b, (int)sizek);
    for (uint32_t i = 0; i < sizek; i++) {
        uint8_t t = r_byte(r); buf_write_byte(b, t & 0x3F);
        switch (t) {
            case 0: break;
            case 1: buf_write_byte(b, r_byte(r)); break;
            case 3: buf_write_double(b, r_double(r)); break;
            case 0x13: { int64_t v = r_int64(r); if (obfuscated) v = decrypt_integer(v); buf_write_int64(b, v); break; }
            case 4: case 0x14: { size_t kl; const uint8_t *ks = r_str(r, &kl); w_str(b, ks, kl); break; }
        }
    }
    uint32_t sizeup = r_uint32(r); buf_write_int(b, (int)sizeup);
    for (uint32_t i = 0; i < sizeup; i++) { buf_write_byte(b, r_byte(r)); buf_write_byte(b, r_byte(r)); }
    uint32_t sizep = r_uint32(r); buf_write_int(b, (int)sizep);
    for (uint32_t i = 0; i < sizep; i++) process_proto(r, b);
    r_int(r); r_int(r); r_int(r); buf_write_int(b, 0); buf_write_int(b, 0); buf_write_int(b, 0);
}

static int L_decrypt(lua_State *L) {
    size_t len; const uint8_t *data = (const uint8_t *)luaL_checklstring(L, 1, &len);
    if (len < 33 || memcmp(data, "\x1bLua", 4) != 0) return luaL_error(L, "Invalid signature");
    Reader r = { data, data + len }; r.p += 32; uint8_t nup = r_byte(&r);
    Buffer b; buf_init(&b);
    buf_write(&b, "\x1bLua\x53\x00\x19\x93\r\n\x1a\n\x04\x08\x04\x08\x08\x78\x56\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x77\x40", 33);
    buf_write_byte(&b, nup); process_proto(&r, &b);
    lua_pushlstring(L, (const char *)b.data, b.size); buf_free(&b); return 1;
}

int luaopen_luadec(lua_State *L) {
    static const struct luaL_Reg funcs[] = { {"decrypt", L_decrypt}, {NULL, NULL} };
    luaL_newlib(L, funcs); return 1;
}
