#ifndef lobfuscator_h
#define lobfuscator_h

#include "llimits.h"
#include "lua.h"
#include "lobject.h"

/*
** Commercial Obfuscation Keys
*/
#define LUA_CONST_XOR 0x8F
#define LUA_CUSTOM_SIGNATURE "\x1bLUAX"

#include <stdint.h>

#define ENCRYPT_INST(i, idx, seed) encrypt_instruction(i, idx, seed)
#define DECRYPT_INST(i, idx, seed) decrypt_instruction(i, idx, seed)

static inline uint32_t encrypt_instruction(uint32_t i, int idx, uint32_t seed) {
  uint32_t k = seed ^ ((uint32_t)idx * 0x9E3779B9U);
  i ^= k;
  i = (i << 13) | (i >> 19);
  i += k;
  return i;
}

static inline uint32_t decrypt_instruction(uint32_t i, int idx, uint32_t seed) {
  uint32_t k = seed ^ ((uint32_t)idx * 0x9E3779B9U);
  i -= k;
  i = (i >> 13) | (i << 19);
  i ^= k;
  return i;
}

/* Numerical Obfuscation */
#define LUA_INT_XOR       0xDEADBEEFCAFEBABEULL
#define LUA_INT_ADD       0x123456789ABCDEF0ULL
#define LUA_INT_MUL       3ULL
#define LUA_INT_MUL_INV   0xaaaaaaaaaaaaaaabULL

#define ENCRYPT_INT(i) (((((unsigned long long)(i)) * LUA_INT_MUL) + LUA_INT_ADD) ^ LUA_INT_XOR)
#define DECRYPT_INT(i) (((((unsigned long long)(i)) ^ LUA_INT_XOR) - LUA_INT_ADD) * LUA_INT_MUL_INV)


#define LUA_FLT_XOR       0xFEEDFACEDEADBEEFULL
#define LUA_FLT_ADD       12345.6789
#define LUA_FLT_MUL       3.14159265

#define DECRYPT_FLT_VAL(n) decrypt_float_obf(n)
#define ENCRYPT_FLT_VAL(n) encrypt_float_obf(n)

static lua_Number decrypt_float_obf(lua_Number n) {
  union { lua_Number f; unsigned long long i; } u;
  u.f = n;
  u.i ^= LUA_FLT_XOR;
  return (u.f - LUA_FLT_ADD) / LUA_FLT_MUL;
}

static lua_Number encrypt_float_obf(lua_Number n) {
  union { lua_Number f; unsigned long long i; } u;
  u.f = n * LUA_FLT_MUL + LUA_FLT_ADD;
  u.i ^= LUA_FLT_XOR;
  return u.f;
}

/* Obfuscator functions */
void obfuscate_proto(lua_State *L, Proto *f, int encrypt_strings);
void lua_security_check(void);
void lua_start_security_thread(void);

#endif
