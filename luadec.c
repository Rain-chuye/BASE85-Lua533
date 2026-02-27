#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "lua.h"
#include "lauxlib.h"

/* --- Pro VM Constants & Opcodes --- */

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

typedef enum {
    OP_MOVE, OP_LOADK, OP_LOADKX, OP_LOADBOOL, OP_LOADNIL, OP_GETUPVAL,
    OP_GETTABUP, OP_GETTABLE, OP_SETTABUP, OP_SETUPVAL, OP_SETTABLE,
    OP_NEWTABLE, OP_SELF, OP_ADD, OP_SUB, OP_MUL, OP_MOD, OP_POW,
    OP_DIV, OP_IDIV, OP_BAND, OP_BOR, OP_BXOR, OP_SHL, OP_SHR,
    OP_UNM, OP_BNOT, OP_NOT, OP_LEN, OP_CONCAT, OP_JMP, OP_EQ,
    OP_LT, OP_LE, OP_TEST, OP_TESTSET, OP_CALL, OP_TAILCALL,
    OP_RETURN, OP_FORLOOP, OP_FORPREP, OP_TFORCALL, OP_TFORLOOP,
    OP_SETLIST, OP_CLOSURE, OP_VARARG, OP_EXTRAARG,
    /* Pro specific */
    OP_TBC, OP_NEWARRAY, OP_TFOREACH, OP_TERNARY, OP_VIRTUAL,
    OP_FUSE_GETSUB, OP_FUSE_GETADD, OP_FUSE_GETGETSUB, OP_FAST_DIST,
    OP_FUSE_NOP, OP_FUSE_PARTICLE_DIST, OP_FUSE_ADD_TO_FIELD, OP_VARARGPREP
} OpCode;

/* --- Base85 Decryption Logic --- */

static const char B85_ALPHABET_MASTER[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!#$%&()*+-;<=>?@^_`{|}~";

typedef struct { unsigned int x, y, z, w; } ChuyeXorState;

static unsigned int chuye_xorshift128(ChuyeXorState *s) {
    unsigned int t = s->x ^ (s->x << 11);
    s->x = s->y; s->y = s->z; s->z = s->w;
    return s->w = s->w ^ (s->w >> 19) ^ t ^ (t >> 8);
}

static void shuffle_alphabet(char *alphabet, unsigned int seed) {
    seed ^= 0x12345678;
    ChuyeXorState s = {seed, seed ^ 0x92D68CA2, seed ^ 0x475EAD11, seed ^ 0x6E0323B9};
    int len = (int)strlen(alphabet);
    for (int pass = 0; pass < 3; pass++) {
        for (int i = len - 1; i > 0; i--) {
            int j = chuye_xorshift128(&s) % (i + 1);
            char t = alphabet[i]; alphabet[i] = alphabet[j]; alphabet[j] = t;
        }
        s.x ^= 0x55555555; s.y ^= 0xAAAAAAAA;
    }
}

static int b85_value(const char *alphabet, char c) {
    const char *p = strchr(alphabet, c);
    return p ? (int)(p - alphabet) : -1;
}

static unsigned char* decrypt_pro_base85(const char *input, size_t in_len, size_t *out_len) {
    if (in_len < 8) return NULL;
    unsigned int seed = 0;
    for (int i = 0; i < 8; i++) {
        int val = b85_value(B85_ALPHABET_MASTER, input[i]);
        if (val == -1) return NULL;
        seed |= ((unsigned int)(val & 0x0F) << (i * 4));
    }
    ChuyeXorState s = {seed, seed ^ 0x92D68CA2, seed ^ 0x475EAD11, seed ^ 0x6E0323B9};
    char alphabet[86]; memcpy(alphabet, B85_ALPHABET_MASTER, 85); alphabet[85] = '\0';
    shuffle_alphabet(alphabet, seed);
    unsigned char *decoded = (unsigned char *)malloc(in_len + 1);
    if (!decoded) return NULL;
    size_t di = 0; unsigned char unit[5]; int ui = 0; size_t in_pos = 8;
    while (in_pos < in_len) {
        if (chuye_xorshift128(&s) % 13 == 0) { chuye_xorshift128(&s); in_pos++; if (in_pos >= in_len) break; }
        if (input[in_pos] == '.') break;
        unsigned int r_data = chuye_xorshift128(&s);
        int val = b85_value(alphabet, input[in_pos++]);
        if (val == -1) continue;
        val = (val + 85 - (int)(r_data % 85)) % 85;
        unit[ui++] = (unsigned char)val;
        if (ui == 5) {
            unsigned long long v = 0;
            for (int j = 0; j < 5; j++) v = v * 85 + unit[j];
            decoded[di++] = (unsigned char)((v >> 24) & 0xFF);
            decoded[di++] = (unsigned char)((v >> 16) & 0xFF);
            decoded[di++] = (unsigned char)((v >> 8) & 0xFF);
            decoded[di++] = (unsigned char)(v & 0xFF);
            ui = 0;
        }
    }
    if (ui > 0) {
        unsigned long long v = 0;
        for (int j = 0; j < ui; j++) v = v * 85 + unit[j];
        for (int j = 0; j < 5 - ui; j++) v = v * 85 + 84;
        for (int j = 0; j < ui - 1; j++) decoded[di++] = (unsigned char)((v >> (24 - j * 8)) & 0xFF);
    }
    ChuyeXorState s2 = {seed, seed ^ 0x92D68CA2, seed ^ 0x475EAD11, seed ^ 0x6E0323B9};
    for (size_t i = 0; i < di; i++) {
        unsigned int r = chuye_xorshift128(&s2);
        int rot = (r >> 8) & 7;
        unsigned char b = decoded[i];
        b = (unsigned char)((b >> rot) | (b << (8 - rot)));
        b ^= (unsigned char)(r & 0xFF);
        decoded[i] = b;
    }
    if (di >= 12 && memcmp(decoded, "CHYE", 4) == 0) {
        size_t data_len = di - 12;
        unsigned char *data = (unsigned char *)malloc(data_len);
        if (data) { memcpy(data, decoded + 12, data_len); free(decoded); *out_len = data_len; return data; }
    }
    free(decoded); return NULL;
}

/* --- Core Decryption & Serialization --- */

static inline uint32_t decrypt_inst(uint32_t i, int idx, uint32_t seed) {
    uint32_t k = seed ^ ((uint32_t)idx * 0x9E3779B9U);
    i -= k; i = (i >> 13) | (i << 19); i ^= k; return i;
}

static inline int64_t decrypt_int(int64_t i) {
    return (int64_t)((((uint64_t)i ^ 0xDEADBEEFCAFEBABEULL) - 0x123456789ABCDEF0ULL) * 0xaaaaaaaaaaaaaaabULL);
}

typedef struct { uint8_t *data; size_t size; size_t cap; } Buffer;
static void buf_init(Buffer *b) { b->data = NULL; b->size = b->cap = 0; }
static void buf_free(Buffer *b) { free(b->data); }
static void buf_write(Buffer *b, const void *data, size_t len) {
    if (b->size + len > b->cap) { b->cap = (b->cap + len) * 2 + 1024; b->data = (uint8_t*)realloc(b->data, b->cap); }
    memcpy(b->data + b->size, data, len); b->size += len;
}
static void buf_w8(Buffer *b, uint8_t v) { buf_write(b, &v, 1); }
static void buf_w32(Buffer *b, uint32_t v) { buf_write(b, &v, 4); }
static void buf_w64(Buffer *b, uint64_t v) { buf_write(b, &v, 8); }
static void buf_wf(Buffer *b, double v) { buf_write(b, &v, 8); }

typedef struct { const uint8_t *p; const uint8_t *end; } Reader;
static uint8_t r8(Reader *r) { return *r->p++; }
static int ri(Reader *r) { int v; memcpy(&v, r->p, sizeof(int)); r->p += sizeof(int); return v; }
static uint32_t r32(Reader *r) { uint32_t v; memcpy(&v, r->p, 4); r->p += 4; return v; }
static int64_t r64(Reader *r) { int64_t v; memcpy(&v, r->p, 8); r->p += 8; return v; }
static double rf(Reader *r) { double v; memcpy(&v, r->p, 8); r->p += 8; return v; }
static const uint8_t* rstr(Reader *r, size_t *len) {
    uint8_t s = r8(r);
    if (s == 0xFF) { *len = r32(r); const uint8_t *ret = r->p; r->p += (*len - 1); return ret; }
    if (s == 0) { r32(r); *len = 0; return NULL; }
    *len = s; const uint8_t *ret = r->p; r->p += (s - 1); return ret;
}
static void wstr(Buffer *b, const uint8_t *s, size_t len) {
    if (len == 0) buf_w8(b, 0);
    else if (len < 0xFF) { buf_w8(b, (uint8_t)len); buf_write(b, s, len - 1); }
    else { buf_w8(b, 0xFF); buf_w32(b, (uint32_t)len); buf_write(b, s, len - 1); }
}

static void process_proto(Reader *r, Buffer *b) {
    size_t sl; const uint8_t *src = rstr(r, &sl); wstr(b, src, sl);
    buf_w32(b, ri(r)); buf_w32(b, ri(r));
    buf_w8(b, r8(r)); buf_w8(b, r8(r)); buf_w8(b, r8(r));
    uint8_t obf = r8(r); ri(r); uint32_t seed = r32(r);
    uint8_t inv[128]; memset(inv, 0, 128);
    if (r8(r)) { uint8_t map[128]; memcpy(map, r->p, 64); r->p += 64; for (int i = 0; i < 64; i++) inv[map[i]] = (uint8_t)i; }
    uint32_t sc = r32(r); uint32_t *code = (uint32_t*)malloc(sc * 4); memcpy(code, r->p, sc * 4); r->p += sc * 4;
    uint32_t svc = r32(r); uint32_t *vcode = (uint32_t*)malloc(svc * 4); memcpy(vcode, r->p, svc * 4); r->p += svc * 4;
    if (obf) {
        for (uint32_t i = 0; i < sc; i++) {
            code[i] = decrypt_inst(code[i], (int)i, seed);
            uint8_t op = inv[GET_OPCODE(code[i])];
            if (op == OP_VIRTUAL) {
                int vi = GETARG_Ax(code[i]);
                uint32_t vc = decrypt_inst(vcode[vi], vi, seed);
                for (uint32_t j = 0; j < vc; j++) {
                    uint32_t vinst = ~decrypt_inst(vcode[vi+1+j], vi+1+j, seed);
                    uint32_t dec = inv[vinst&0x3F]|(((vinst>>15)&0xFF)<<6)|(((vinst>>6)&0x1FF)<<23)|(((vinst>>23)&0x1FF)<<14);
                    if (i+j < sc) code[i+j] = dec;
                }
            } else if (op == OP_FUSE_GETSUB && i+1 < sc) {
                uint32_t next = decrypt_inst(code[i+1], (int)i+1, seed);
                int ra = GETARG_A(code[i]), rb = GETARG_B(code[i]), rc = GETARG_C(code[i]), rd = GETARG_Ax(next);
                code[i] = CREATE_ABC(OP_GETTABLE, ra, rb, rc); code[i+1] = CREATE_ABC(OP_SUB, ra, ra, rd); i++;
            } else if (op == OP_FUSE_GETADD && i+1 < sc) {
                uint32_t next = decrypt_inst(code[i+1], (int)i+1, seed);
                int ra = GETARG_A(code[i]), rb = GETARG_B(code[i]), rc = GETARG_C(code[i]), rd = GETARG_Ax(next);
                code[i] = CREATE_ABC(OP_GETTABLE, ra, rb, rc); code[i+1] = CREATE_ABC(OP_ADD, ra, ra, rd); i++;
            } else if (op == OP_FUSE_NOP) code[i] = CREATE_ABC(OP_MOVE, 0, 0, 0);
            else SET_OPCODE(code[i], op);
        }
    }
    buf_w32(b, sc); buf_write(b, code, sc * 4); free(code); free(vcode);
    uint32_t sk = r32(r); buf_w32(b, sk);
    for (uint32_t i = 0; i < sk; i++) {
        uint8_t t = r8(r); buf_w8(b, t & 0x3F);
        switch (t) {
            case 0: break;
            case 1: buf_w8(b, r8(r)); break;
            case 3: buf_wf(b, rf(r)); break;
            case 0x13: { int64_t v = r64(r); if (obf) v = decrypt_int(v); buf_w64(b, v); break; }
            case 4: case 0x14: { size_t kl; const uint8_t *ks = rstr(r, &kl); wstr(b, ks, kl); break; }
        }
    }
    uint32_t su = r32(r); buf_w32(b, su);
    for (uint32_t i = 0; i < su; i++) { buf_w8(b, r8(r)); buf_w8(b, r8(r)); }
    uint32_t sp = r32(r); buf_w32(b, sp);
    for (uint32_t i = 0; i < sp; i++) process_proto(r, b);
    r32(r); r32(r); r32(r); buf_w32(b, 0); buf_w32(b, 0); buf_w32(b, 0);
}

static int L_decrypt(lua_State *L) {
    size_t len; const char *raw = luaL_checklstring(L, 1, &len);
    size_t ol = 0; unsigned char *data = decrypt_pro_base85(raw, len, &ol);
    if (!data) { if (len >= 33 && memcmp(raw, "\x1bLua", 4) == 0) { data = malloc(len); memcpy(data, raw, len); ol = len; } else return luaL_error(L, "Invalid input"); }
    Reader r = { data, data + ol }; r.p += 33; uint8_t nup = r8(&r); Buffer b; buf_init(&b);
    buf_write(&b, "\x1bLua\x53\x00\x19\x93\r\n\x1a\n\x04\x08\x04\x08\x08\x78\x56\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x77\x40", 33);
    buf_w8(&b, nup); process_proto(&r, &b);
    lua_pushlstring(L, (const char *)b.data, b.size); buf_free(&b); free(data); return 1;
}

int luaopen_luadec(lua_State *L) {
    static const struct luaL_Reg funcs[] = { {"decrypt", L_decrypt}, {NULL, NULL} };
    luaL_newlib(L, funcs); return 1;
}
