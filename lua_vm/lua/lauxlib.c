/*
** $Id: lauxlib.c,v 1.286 2016/01/08 15:33:09 roberto Exp $
** Auxiliary functions for building Lua libraries
** See Copyright Notice in lua.h
*/

#define lauxlib_c
#define LUA_LIB

#include "lprefix.h"


#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


/*
** This file uses only the official API of Lua.
** Any function declared here could be written as an application function.
*/

#include "lua.h"

#include "lauxlib.h"

static const char B85_ALPHABET_MASTER[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!#$%&()*+-;<=>?@^_`{|}~";

typedef struct {
    unsigned int x, y, z, w;
} ChuyeXorState;

static unsigned int chuye_xorshift128(ChuyeXorState *s) {
    unsigned int t = s->x ^ (s->x << 11);
    s->x = s->y; s->y = s->z; s->z = s->w;
    return s->w = s->w ^ (s->w >> 19) ^ t ^ (t >> 8);
}

static void shuffle_alphabet(char *alphabet, unsigned int seed) {
    seed ^= 0x12345678; /* Secret Salt */
    ChuyeXorState s = {seed, seed ^ 0x92D68CA2, seed ^ 0x475EAD11, seed ^ 0x6E0323B9};
    int len = (int)strlen(alphabet);
    /* Multi-pass robust shuffle */
    for (int pass = 0; pass < 3; pass++) {
        for (int i = len - 1; i > 0; i--) {
            int j = chuye_xorshift128(&s) % (i + 1);
            char t = alphabet[i];
            alphabet[i] = alphabet[j];
            alphabet[j] = t;
        }
        /* Perturb state between passes */
        s.x ^= 0x55555555; s.y ^= 0xAAAAAAAA;
    }
}

/* Advanced LZ77-based compression with Bit-level coding */
typedef struct {
    unsigned char *data;
    size_t pos;
    size_t cap;
    unsigned int bit_buf;
    int bit_cnt;
} ChuyeBitStream;

static void chuye_bs_init(ChuyeBitStream *bs, size_t cap) {
    bs->data = (unsigned char *)malloc(cap);
    bs->pos = 0;
    bs->cap = cap;
    bs->bit_buf = 0;
    bs->bit_cnt = 0;
}

static void chuye_bs_write(ChuyeBitStream *bs, unsigned int val, int bits) {
    bs->bit_buf |= (val << bs->bit_cnt);
    bs->bit_cnt += bits;
    while (bs->bit_cnt >= 8) {
        if (bs->pos >= bs->cap) {
            bs->cap *= 2;
            bs->data = (unsigned char *)realloc(bs->data, bs->cap);
        }
        bs->data[bs->pos++] = (unsigned char)(bs->bit_buf & 0xFF);
        bs->bit_buf >>= 8;
        bs->bit_cnt -= 8;
    }
}

static void chuye_bs_flush(ChuyeBitStream *bs) {
    if (bs->bit_cnt > 0) {
        if (bs->pos >= bs->cap) {
            bs->cap *= 2;
            bs->data = (unsigned char *)realloc(bs->data, bs->cap);
        }
        bs->data[bs->pos++] = (unsigned char)(bs->bit_buf & 0xFF);
    }
}

static void chuye_bs_free(ChuyeBitStream *bs) {
    if (bs->data) free(bs->data);
}

static unsigned int chuye_bs_read(ChuyeBitStream *bs, int bits, const unsigned char *input, size_t len) {
    while (bs->bit_cnt < bits) {
        unsigned int b = (bs->pos < len) ? input[bs->pos++] : 0;
        bs->bit_buf |= (b << bs->bit_cnt);
        bs->bit_cnt += 8;
    }
    unsigned int res = bs->bit_buf & ((1U << bits) - 1);
    bs->bit_buf >>= bits;
    bs->bit_cnt -= bits;
    return res;
}

#define HASH_SIZE 8192
#define MAX_CHAIN 16

static unsigned int hash3(const unsigned char *p) {
    return ((p[0] << 10) ^ (p[1] << 5) ^ p[2]) & (HASH_SIZE - 1);
}

LUALIB_API unsigned char *luaL_compress(const unsigned char *input, size_t len, size_t *out_len) {
    if (len == 0) { *out_len = 0; return NULL; }
    ChuyeBitStream bs;
    chuye_bs_init(&bs, len + 64);

    size_t temp_len = len;
    do {
        unsigned char b = temp_len & 0x7F;
        temp_len >>= 7;
        if (temp_len > 0) b |= 0x80;
        chuye_bs_write(&bs, b, 8);
    } while (temp_len > 0);

    int *head = (int *)malloc(HASH_SIZE * sizeof(int));
    int *prev = (int *)malloc(len * sizeof(int));
    if (!head || !prev) {
        if (head) free(head);
        if (prev) free(prev);
        chuye_bs_free(&bs);
        return NULL;
    }
    for (int i = 0; i < HASH_SIZE; i++) head[i] = -1;

    size_t in_pos = 0;
    while (in_pos < len) {
        int best_len = 0;
        int best_off = 0;

        if (in_pos + 3 <= len) {
            unsigned int h = hash3(input + in_pos);
            int p_pos = head[h];
            int chain = 0;
            while (p_pos != -1 && chain++ < MAX_CHAIN) {
                if (in_pos - p_pos > 32767) break;
                int l = 0;
                while (l < 266 && in_pos + l < len && input[p_pos + l] == input[in_pos + l]) {
                    l++;
                }
                if (l > best_len) {
                    best_len = l;
                    best_off = (int)(in_pos - p_pos);
                    if (l == 266) break;
                }
                p_pos = prev[p_pos];
            }
        }

        if (best_len >= 3) {
            chuye_bs_write(&bs, 1, 1);
            if (best_len <= 10) {
                chuye_bs_write(&bs, 0, 1);
                chuye_bs_write(&bs, best_len - 3, 3);
            } else {
                chuye_bs_write(&bs, 1, 1);
                chuye_bs_write(&bs, best_len - 11, 8);
            }
            chuye_bs_write(&bs, best_off - 1, 15);
            for (int k = 0; k < best_len; k++) {
                if (in_pos + 3 <= len) {
                    unsigned int h = hash3(input + in_pos);
                    prev[in_pos] = head[h];
                    head[h] = (int)in_pos;
                }
                in_pos++;
            }
        } else {
            chuye_bs_write(&bs, 0, 1);
            chuye_bs_write(&bs, input[in_pos], 8);
            if (in_pos + 3 <= len) {
                unsigned int h = hash3(input + in_pos);
                prev[in_pos] = head[h];
                head[h] = (int)in_pos;
            }
            in_pos++;
        }
    }
    free(head); free(prev);
    chuye_bs_flush(&bs);
    *out_len = bs.pos;
    return bs.data;
}

LUALIB_API unsigned char *luaL_decompress(const unsigned char *input, size_t len, size_t *out_len) {
    if (len == 0) { *out_len = 0; return NULL; }
    ChuyeBitStream bs;
    bs.pos = 0;
    bs.bit_buf = 0;
    bs.bit_cnt = 0;

    size_t orig_len = 0;
    int shift = 0;
    unsigned char b;
    do {
        b = input[bs.pos++];
        orig_len |= (size_t)(b & 0x7F) << shift;
        shift += 7;
    } while (b & 0x80);

    unsigned char *output = (unsigned char *)malloc(orig_len + 1);
    if (!output) return NULL;
    size_t out_pos = 0;

    while (out_pos < orig_len) {
        if (chuye_bs_read(&bs, 1, input, len)) {
            int match_len;
            if (chuye_bs_read(&bs, 1, input, len) == 0)
                match_len = chuye_bs_read(&bs, 3, input, len) + 3;
            else
                match_len = chuye_bs_read(&bs, 8, input, len) + 11;
            int off = chuye_bs_read(&bs, 15, input, len) + 1;
            if (off > (int)out_pos) { free(output); return NULL; }
            for (int i = 0; i < match_len; i++) {
                output[out_pos] = output[out_pos - off];
                out_pos++;
            }
        } else {
            output[out_pos++] = (unsigned char)chuye_bs_read(&bs, 8, input, len);
        }
    }
    *out_len = out_pos;
    return output;
}

LUALIB_API unsigned int luaL_crc32(const unsigned char *data, size_t len) {
    unsigned int crc = 0xFFFFFFFF;
    for (size_t i = 0; i < len; i++) {
        crc ^= data[i];
        for (int j = 0; j < 8; j++) {
            crc = (crc >> 1) ^ (0xEDB88320 & (-(crc & 1)));
        }
    }
    return ~crc;
}

static int b85_value(const char *alphabet, char c) {
    const char *p = strchr(alphabet, c);
    if (p) return (int)(p - alphabet);
    return -1;
}

static unsigned int recover_seed(const char *in) {
    unsigned int seed = 0;
    for (int i = 0; i < 8; i++) {
        int val = b85_value(B85_ALPHABET_MASTER, in[i]);
        if (val == -1) return 0;
        seed |= ((unsigned int)(val & 0x0F) << (i * 4));
    }
    return seed;
}

LUALIB_API unsigned char *luaL_decrypt_chuye(const char *input, size_t in_len, size_t *out_len) {
    if (in_len < 8) return NULL;
    unsigned int seed = recover_seed(input);
    ChuyeXorState s = {seed, seed ^ 0x92D68CA2, seed ^ 0x475EAD11, seed ^ 0x6E0323B9};

    char alphabet[86];
    memcpy(alphabet, B85_ALPHABET_MASTER, 85);
    alphabet[85] = '\0';
    shuffle_alphabet(alphabet, seed);

    unsigned char *decoded = (unsigned char *)malloc(in_len + 1);
    if (!decoded) return NULL;
    size_t di = 0;
    unsigned char unit[5];
    int ui = 0;

    size_t in_pos = 8;
    while (in_pos < in_len) {
        unsigned int r_noise = chuye_xorshift128(&s);
        if (r_noise % 13 == 0) {
            chuye_xorshift128(&s); // Skip noise value state
            in_pos++;
            if (in_pos >= in_len) break;
        }
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
        for (int j = 0; j < ui - 1; j++) {
            decoded[di++] = (unsigned char)((v >> (24 - j * 8)) & 0xFF);
        }
    }

    // Stateful Stream Decryption
    ChuyeXorState s2 = {seed, seed ^ 0x92D68CA2, seed ^ 0x475EAD11, seed ^ 0x6E0323B9};
    for (size_t i = 0; i < di; i++) {
        unsigned int r = chuye_xorshift128(&s2);
        int rot = (r >> 8) & 7;
        unsigned char b = decoded[i];
        b = (unsigned char)((b >> rot) | (b << (8 - rot)));
        b ^= (unsigned char)(r & 0xFF);
        decoded[i] = b;
    }

    *out_len = di;
    return decoded;
}

LUALIB_API unsigned char *luaL_chuye_decode_and_decrypt(lua_State *L, const char *src, size_t len, size_t *outlen) {
    size_t decoded_len;
    unsigned char *decoded = luaL_decrypt_chuye(src, len, &decoded_len);
    if (!decoded || decoded_len < 12) {
        if (decoded) {
            memset(decoded, 0, decoded_len);
            free(decoded);
        }
        return NULL;
    }

    if (memcmp(decoded, "CHYE", 4) != 0) {
        memset(decoded, 0, decoded_len);
        free(decoded);
        return NULL;
    }

    // Header check (optional: CRC verification could be done here)
    // uint32_t expected_crc = (decoded[4] << 24) | (decoded[5] << 16) | (decoded[6] << 8) | decoded[7];

    size_t data_len = decoded_len - 12;
    unsigned char *data = (unsigned char *)malloc(data_len);
    if (!data) {
        memset(decoded, 0, decoded_len);
        free(decoded);
        return NULL;
    }

    memcpy(data, decoded + 12, data_len);
    memset(decoded, 0, decoded_len);
    free(decoded);

    // Outer Decryption removed as it's now handled in luaL_decrypt_chuye with ChuyeXorState

    *outlen = data_len;
    return data;
}


/*
** {======================================================
** Traceback
** =======================================================
*/


#define LEVELS1	10	/* size of the first part of the stack */
#define LEVELS2	11	/* size of the second part of the stack */



/*
** search for 'objidx' in table at index -1.
** return 1 + string at top if find a good name.
*/
static int findfield (lua_State *L, int objidx, int level) {
  if (level == 0 || !lua_istable(L, -1))
    return 0;  /* not found */
  lua_pushnil(L);  /* start 'next' loop */
  while (lua_next(L, -2)) {  /* for each pair in table */
    if (lua_type(L, -2) == LUA_TSTRING) {  /* ignore non-string keys */
      if (lua_rawequal(L, objidx, -1)) {  /* found object? */
        lua_pop(L, 1);  /* remove value (but keep name) */
        return 1;
      }
      else if (findfield(L, objidx, level - 1)) {  /* try recursively */
        lua_remove(L, -2);  /* remove table (but keep name) */
        lua_pushliteral(L, ".");
        lua_insert(L, -2);  /* place '.' between the two names */
        lua_concat(L, 3);
        return 1;
      }
    }
    lua_pop(L, 1);  /* remove value */
  }
  return 0;  /* not found */
}


/*
** Search for a name for a function in all loaded modules
** (registry._LOADED).
*/
static int pushglobalfuncname (lua_State *L, lua_Debug *ar) {
  int top = lua_gettop(L);
  lua_getinfo(L, "f", ar);  /* push function */
  lua_getfield(L, LUA_REGISTRYINDEX, "_LOADED");
  if (findfield(L, top + 1, 2)) {
    const char *name = lua_tostring(L, -1);
    if (strncmp(name, "_G.", 3) == 0) {  /* name start with '_G.'? */
      lua_pushstring(L, name + 3);  /* push name without prefix */
      lua_remove(L, -2);  /* remove original name */
    }
    lua_copy(L, -1, top + 1);  /* move name to proper place */
    lua_pop(L, 2);  /* remove pushed values */
    return 1;
  }
  else {
    lua_settop(L, top);  /* remove function and global table */
    return 0;
  }
}


static void pushfuncname (lua_State *L, lua_Debug *ar) {
  if (pushglobalfuncname(L, ar)) {  /* try first a global name */
    lua_pushfstring(L, "function '%s'", lua_tostring(L, -1));
    lua_remove(L, -2);  /* remove name */
  }
  else if (*ar->namewhat != '\0')  /* is there a name from code? */
    lua_pushfstring(L, "%s '%s'", ar->namewhat, ar->name);  /* use it */
  else if (*ar->what == 'm')  /* main? */
      lua_pushliteral(L, "main chunk");
  else if (*ar->what != 'C')  /* for Lua functions, use <file:line> */
    lua_pushfstring(L, "function <%s:%d>", ar->short_src, ar->linedefined);
  else  /* nothing left... */
    lua_pushliteral(L, "?");
}


static int lastlevel (lua_State *L) {
  lua_Debug ar;
  int li = 1, le = 1;
  /* find an upper bound */
  while (lua_getstack(L, le, &ar)) { li = le; le *= 2; }
  /* do a binary search */
  while (li < le) {
    int m = (li + le)/2;
    if (lua_getstack(L, m, &ar)) li = m + 1;
    else le = m;
  }
  return le - 1;
}


LUALIB_API void luaL_traceback (lua_State *L, lua_State *L1,
                                const char *msg, int level) {
  lua_Debug ar;
  int top = lua_gettop(L);
  int last = lastlevel(L1);
  int n1 = (last - level > LEVELS1 + LEVELS2) ? LEVELS1 : -1;
  if (msg)
    lua_pushfstring(L, "%s\n", msg);
  luaL_checkstack(L, 10, NULL);
  lua_pushliteral(L, "stack traceback:");
  while (lua_getstack(L1, level++, &ar)) {
    if (n1-- == 0) {  /* too many levels? */
      lua_pushliteral(L, "\n\t...");  /* add a '...' */
      level = last - LEVELS2 + 1;  /* and skip to last ones */
    }
    else {
      lua_getinfo(L1, "Slnt", &ar);
      lua_pushfstring(L, "\n\t%s:", ar.short_src);
      if (ar.currentline > 0)
        lua_pushfstring(L, "%d:", ar.currentline);
      lua_pushliteral(L, " in ");
      pushfuncname(L, &ar);
      if (ar.istailcall)
        lua_pushliteral(L, "\n\t(...tail calls...)");
      lua_concat(L, lua_gettop(L) - top);
    }
  }
  lua_concat(L, lua_gettop(L) - top);
}

/* }====================================================== */


/*
** {======================================================
** Error-report functions
** =======================================================
*/

LUALIB_API int luaL_argerror (lua_State *L, int arg, const char *extramsg) {
  lua_Debug ar;
  if (!lua_getstack(L, 0, &ar))  /* no stack frame? */
    return luaL_error(L, "第 #%d 个参数错误 (%s)", arg, extramsg);
  lua_getinfo(L, "n", &ar);
  if (strcmp(ar.namewhat, "method") == 0) {
    arg--;  /* do not count 'self' */
    if (arg == 0)  /* error is in the self argument itself? */
      return luaL_error(L, "对错误的 self 调用 '%s' (%s)",
                           ar.name, extramsg);
  }
  if (ar.name == NULL)
    ar.name = (pushglobalfuncname(L, &ar)) ? lua_tostring(L, -1) : "?";
  return luaL_error(L, "给 '%s' 传递的第 #%d 个参数错误 (%s)",
                        ar.name, arg, extramsg);
}


static int typeerror (lua_State *L, int arg, const char *tname) {
  const char *msg;
  const char *typearg;  /* name for the type of the actual argument */
  if (luaL_getmetafield(L, arg, "__name") == LUA_TSTRING)
    typearg = lua_tostring(L, -1);  /* use the given type name */
  else if (lua_type(L, arg) == LUA_TLIGHTUSERDATA)
    typearg = "轻量级用户数据";  /* special name for messages */
  else
    typearg = luaL_typename(L, arg);  /* standard name */
  msg = lua_pushfstring(L, "期望为 %s，得到的是 %s", tname, typearg);
  return luaL_argerror(L, arg, msg);
}


static void tag_error (lua_State *L, int arg, int tag) {
  typeerror(L, arg, lua_typename(L, tag));
}


/*
** The use of 'lua_pushfstring' ensures this function does not
** need reserved stack space when called.
*/
LUALIB_API void luaL_where (lua_State *L, int level) {
  lua_Debug ar;
  if (lua_getstack(L, level, &ar)) {  /* check function at level */
    lua_getinfo(L, "Sl", &ar);  /* get info about it */
    if (ar.currentline > 0) {  /* is there info? */
      lua_pushfstring(L, "%s:%d: ", ar.short_src, ar.currentline);
      return;
    }
  }
  lua_pushfstring(L, "");  /* else, no information available... */
}


/*
** Again, the use of 'lua_pushvfstring' ensures this function does
** not need reserved stack space when called. (At worst, it generates
** an error with "stack overflow" instead of the given message.)
*/
LUALIB_API int luaL_error (lua_State *L, const char *fmt, ...) {
  va_list argp;
  va_start(argp, fmt);
  luaL_where(L, 1);
  lua_pushvfstring(L, fmt, argp);
  va_end(argp);
  lua_concat(L, 2);
  return lua_error(L);
}


LUALIB_API int luaL_fileresult (lua_State *L, int stat, const char *fname) {
  int en = errno;  /* calls to Lua API may change this value */
  if (stat) {
    lua_pushboolean(L, 1);
    return 1;
  }
  else {
    lua_pushnil(L);
    if (fname)
      lua_pushfstring(L, "%s: %s", fname, strerror(en));
    else
      lua_pushstring(L, strerror(en));
    lua_pushinteger(L, en);
    return 3;
  }
}


#if !defined(l_inspectstat)	/* { */

#if defined(LUA_USE_POSIX)

#include <sys/wait.h>

/*
** use appropriate macros to interpret 'pclose' return status
*/
#define l_inspectstat(stat,what)  \
   if (WIFEXITED(stat)) { stat = WEXITSTATUS(stat); } \
   else if (WIFSIGNALED(stat)) { stat = WTERMSIG(stat); what = "signal"; }

#else

#define l_inspectstat(stat,what)  /* no op */

#endif

#endif				/* } */


LUALIB_API int luaL_execresult (lua_State *L, int stat) {
  const char *what = "exit";  /* type of termination */
  if (stat == -1)  /* error? */
    return luaL_fileresult(L, 0, NULL);
  else {
    l_inspectstat(stat, what);  /* interpret result */
    if (*what == 'e' && stat == 0)  /* successful termination? */
      lua_pushboolean(L, 1);
    else
      lua_pushnil(L);
    lua_pushstring(L, what);
    lua_pushinteger(L, stat);
    return 3;  /* return true/nil,what,code */
  }
}

/* }====================================================== */


/*
** {======================================================
** Userdata's metatable manipulation
** =======================================================
*/

LUALIB_API int luaL_newmetatable (lua_State *L, const char *tname) {
  if (luaL_getmetatable(L, tname) != LUA_TNIL)  /* name already in use? */
    return 0;  /* leave previous value on top, but return 0 */
  lua_pop(L, 1);
  lua_createtable(L, 0, 2);  /* create metatable */
  lua_pushstring(L, tname);
  lua_setfield(L, -2, "__name");  /* metatable.__name = tname */
  lua_pushvalue(L, -1);
  lua_setfield(L, LUA_REGISTRYINDEX, tname);  /* registry.name = metatable */
  return 1;
}


LUALIB_API void luaL_setmetatable (lua_State *L, const char *tname) {
  luaL_getmetatable(L, tname);
  lua_setmetatable(L, -2);
}


LUALIB_API void *luaL_testudata (lua_State *L, int ud, const char *tname) {
  void *p = lua_touserdata(L, ud);
  if (p != NULL) {  /* value is a userdata? */
    if (lua_getmetatable(L, ud)) {  /* does it have a metatable? */
      luaL_getmetatable(L, tname);  /* get correct metatable */
      if (!lua_rawequal(L, -1, -2))  /* not the same? */
        p = NULL;  /* value is a userdata with wrong metatable */
      lua_pop(L, 2);  /* remove both metatables */
      return p;
    }
  }
  return NULL;  /* value is not a userdata with a metatable */
}


LUALIB_API void *luaL_checkudata (lua_State *L, int ud, const char *tname) {
  void *p = luaL_testudata(L, ud, tname);
  if (p == NULL) typeerror(L, ud, tname);
  return p;
}

/* }====================================================== */


/*
** {======================================================
** Argument check functions
** =======================================================
*/

LUALIB_API int luaL_checkoption (lua_State *L, int arg, const char *def,
                                 const char *const lst[]) {
  const char *name = (def) ? luaL_optstring(L, arg, def) :
                             luaL_checkstring(L, arg);
  int i;
  for (i=0; lst[i]; i++)
    if (strcmp(lst[i], name) == 0)
      return i;
  return luaL_argerror(L, arg,
                       lua_pushfstring(L, "invalid option '%s'", name));
}


/*
** Ensures the stack has at least 'space' extra slots, raising an error
** if it cannot fulfill the request. (The error handling needs a few
** extra slots to format the error message. In case of an error without
** this extra space, Lua will generate the same 'stack overflow' error,
** but without 'msg'.)
*/
LUALIB_API void luaL_checkstack (lua_State *L, int space, const char *msg) {
  if (!lua_checkstack(L, space)) {
    if (msg)
      luaL_error(L, "栈溢出 (%s)", msg);
    else
      luaL_error(L, "栈溢出");
  }
}


LUALIB_API void luaL_checktype (lua_State *L, int arg, int t) {
  if (lua_type(L, arg) != t)
    tag_error(L, arg, t);
}


LUALIB_API void luaL_checkany (lua_State *L, int arg) {
  if (lua_type(L, arg) == LUA_TNONE)
    luaL_argerror(L, arg, "value expected");
}


LUALIB_API const char *luaL_checklstring (lua_State *L, int arg, size_t *len) {
  const char *s = lua_tolstring(L, arg, len);
  if (!s) tag_error(L, arg, LUA_TSTRING);
  return s;
}


LUALIB_API const char *luaL_optlstring (lua_State *L, int arg,
                                        const char *def, size_t *len) {
  if (lua_isnoneornil(L, arg)) {
    if (len)
      *len = (def ? strlen(def) : 0);
    return def;
  }
  else return luaL_checklstring(L, arg, len);
}


LUALIB_API lua_Number luaL_checknumber (lua_State *L, int arg) {
  int isnum;
  lua_Number d = lua_tonumberx(L, arg, &isnum);
  if (!isnum)
    tag_error(L, arg, LUA_TNUMBER);
  return d;
}


LUALIB_API lua_Number luaL_optnumber (lua_State *L, int arg, lua_Number def) {
  return luaL_opt(L, luaL_checknumber, arg, def);
}


static void interror (lua_State *L, int arg) {
  if (lua_isnumber(L, arg))
    luaL_argerror(L, arg, "number has no integer representation");
  else
    tag_error(L, arg, LUA_TNUMBER);
}


LUALIB_API lua_Integer luaL_checkinteger (lua_State *L, int arg) {
  int isnum;
  lua_Integer d = lua_tointegerx(L, arg, &isnum);
  if (!isnum) {
    interror(L, arg);
  }
  return d;
}


LUALIB_API lua_Integer luaL_optinteger (lua_State *L, int arg,
                                                      lua_Integer def) {
  return luaL_opt(L, luaL_checkinteger, arg, def);
}

/* }====================================================== */


/*
** {======================================================
** Generic Buffer manipulation
** =======================================================
*/

/* userdata to box arbitrary data */
typedef struct UBox {
  void *box;
  size_t bsize;
} UBox;


static void *resizebox (lua_State *L, int idx, size_t newsize) {
  void *ud;
  lua_Alloc allocf = lua_getallocf(L, &ud);
  UBox *box = (UBox *)lua_touserdata(L, idx);
  void *temp = allocf(ud, box->box, box->bsize, newsize);
  if (temp == NULL && newsize > 0) {  /* allocation error? */
    resizebox(L, idx, 0);  /* free buffer */
    luaL_error(L, "内存不足以分配缓冲区");
  }
  box->box = temp;
  box->bsize = newsize;
  return temp;
}


static int boxgc (lua_State *L) {
  resizebox(L, 1, 0);
  return 0;
}


static void *newbox (lua_State *L, size_t newsize) {
  UBox *box = (UBox *)lua_newuserdata(L, sizeof(UBox));
  box->box = NULL;
  box->bsize = 0;
  if (luaL_newmetatable(L, "LUABOX")) {  /* creating metatable? */
    lua_pushcfunction(L, boxgc);
    lua_setfield(L, -2, "__gc");  /* metatable.__gc = boxgc */
  }
  lua_setmetatable(L, -2);
  return resizebox(L, -1, newsize);
}


/*
** check whether buffer is using a userdata on the stack as a temporary
** buffer
*/
#define buffonstack(B)	((B)->b != (B)->initb)


/*
** returns a pointer to a free area with at least 'sz' bytes
*/
LUALIB_API char *luaL_prepbuffsize (luaL_Buffer *B, size_t sz) {
  lua_State *L = B->L;
  if (B->size - B->n < sz) {  /* not enough space? */
    char *newbuff;
    size_t newsize = B->size * 2;  /* double buffer size */
    if (newsize - B->n < sz)  /* not big enough? */
      newsize = B->n + sz;
    if (newsize < B->n || newsize - B->n < sz)
      luaL_error(L, "缓冲区太大");
    /* create larger buffer */
    if (buffonstack(B))
      newbuff = (char *)resizebox(L, -1, newsize);
    else {  /* no buffer yet */
      newbuff = (char *)newbox(L, newsize);
      memcpy(newbuff, B->b, B->n * sizeof(char));  /* copy original content */
    }
    B->b = newbuff;
    B->size = newsize;
  }
  return &B->b[B->n];
}


LUALIB_API void luaL_addlstring (luaL_Buffer *B, const char *s, size_t l) {
  if (l > 0) {  /* avoid 'memcpy' when 's' can be NULL */
    char *b = luaL_prepbuffsize(B, l);
    memcpy(b, s, l * sizeof(char));
    luaL_addsize(B, l);
  }
}


LUALIB_API void luaL_addstring (luaL_Buffer *B, const char *s) {
  luaL_addlstring(B, s, strlen(s));
}


LUALIB_API void luaL_pushresult (luaL_Buffer *B) {
  lua_State *L = B->L;
  lua_pushlstring(L, B->b, B->n);
  if (buffonstack(B)) {
    resizebox(L, -2, 0);  /* delete old buffer */
    lua_remove(L, -2);  /* remove its header from the stack */
  }
}


LUALIB_API void luaL_pushresultsize (luaL_Buffer *B, size_t sz) {
  luaL_addsize(B, sz);
  luaL_pushresult(B);
}


LUALIB_API void luaL_addvalue (luaL_Buffer *B) {
  lua_State *L = B->L;
  size_t l;
  const char *s = lua_tolstring(L, -1, &l);
  if (buffonstack(B))
    lua_insert(L, -2);  /* put value below buffer */
  luaL_addlstring(B, s, l);
  lua_remove(L, (buffonstack(B)) ? -2 : -1);  /* remove value */
}


LUALIB_API void luaL_buffinit (lua_State *L, luaL_Buffer *B) {
  B->L = L;
  B->b = B->initb;
  B->n = 0;
  B->size = LUAL_BUFFERSIZE;
}


LUALIB_API char *luaL_buffinitsize (lua_State *L, luaL_Buffer *B, size_t sz) {
  luaL_buffinit(L, B);
  return luaL_prepbuffsize(B, sz);
}

/* }====================================================== */


/*
** {======================================================
** Reference system
** =======================================================
*/

/* index of free-list header */
#define freelist	0


LUALIB_API int luaL_ref (lua_State *L, int t) {
  int ref;
  if (lua_isnil(L, -1)) {
    lua_pop(L, 1);  /* remove from stack */
    return LUA_REFNIL;  /* 'nil' has a unique fixed reference */
  }
  t = lua_absindex(L, t);
  lua_rawgeti(L, t, freelist);  /* get first free element */
  ref = (int)lua_tointeger(L, -1);  /* ref = t[freelist] */
  lua_pop(L, 1);  /* remove it from stack */
  if (ref != 0) {  /* any free element? */
    lua_rawgeti(L, t, ref);  /* remove it from list */
    lua_rawseti(L, t, freelist);  /* (t[freelist] = t[ref]) */
  }
  else  /* no free elements */
    ref = (int)lua_rawlen(L, t) + 1;  /* get a new reference */
  lua_rawseti(L, t, ref);
  return ref;
}


LUALIB_API void luaL_unref (lua_State *L, int t, int ref) {
  if (ref >= 0) {
    t = lua_absindex(L, t);
    lua_rawgeti(L, t, freelist);
    lua_rawseti(L, t, ref);  /* t[ref] = t[freelist] */
    lua_pushinteger(L, ref);
    lua_rawseti(L, t, freelist);  /* t[freelist] = ref */
  }
}

/* }====================================================== */


/*
** {======================================================
** Load functions
** =======================================================
*/

typedef struct LoadF {
  int n;  /* number of pre-read characters */
  FILE *f;  /* file being read */
  char buff[BUFSIZ];  /* area for reading file */
} LoadF;


static const char *getF (lua_State *L, void *ud, size_t *size) {
  LoadF *lf = (LoadF *)ud;
  (void)L;  /* not used */
  if (lf->n > 0) {  /* are there pre-read characters to be read? */
    *size = lf->n;  /* return them (chars already in buffer) */
    lf->n = 0;  /* no more pre-read characters */
  }
  else {  /* read a block from file */
    /* 'fread' can return > 0 *and* set the EOF flag. If next call to
       'getF' called 'fread', it might still wait for user input.
       The next check avoids this problem. */
    if (feof(lf->f)) return NULL;
    *size = fread(lf->buff, 1, sizeof(lf->buff), lf->f);  /* read block */
  }
  return lf->buff;
}


static int errfile (lua_State *L, const char *what, int fnameindex) {
  const char *serr = strerror(errno);
  const char *filename = lua_tostring(L, fnameindex) + 1;
  lua_pushfstring(L, "cannot %s %s: %s", what, filename, serr);
  lua_remove(L, fnameindex);
  return LUA_ERRFILE;
}


static int skipBOM (LoadF *lf) {
  const char *p = "\xEF\xBB\xBF";  /* UTF-8 BOM mark */
  int c;
  lf->n = 0;
  do {
    c = getc(lf->f);
    if (c == EOF || c != *(const unsigned char *)p++) return c;
    lf->buff[lf->n++] = c;  /* to be read by the parser */
  } while (*p != '\0');
  lf->n = 0;  /* prefix matched; discard it */
  return getc(lf->f);  /* return next character */
}


/*
** reads the first character of file 'f' and skips an optional BOM mark
** in its beginning plus its first line if it starts with '#'. Returns
** true if it skipped the first line.  In any case, '*cp' has the
** first "valid" character of the file (after the optional BOM and
** a first-line comment).
*/
static int skipcomment (LoadF *lf, int *cp) {
  int c = *cp = skipBOM(lf);
  if (c == '#') {  /* first line is a comment (Unix exec. file)? */
    do {  /* skip first line */
      c = getc(lf->f);
    } while (c != EOF && c != '\n');
    *cp = getc(lf->f);  /* skip end-of-line, if present */
    return 1;  /* there was a comment */
  }
  else return 0;  /* no comment */
}

static const char *read_all (lua_State *L, FILE *f, size_t *len) {
    size_t nr;
    luaL_Buffer b;
    luaL_buffinit(L, &b);
    do {  /* read file in chunks of LUAL_BUFFERSIZE bytes */
        char *p = luaL_prepbuffer(&b);
        nr = fread(p, sizeof(char), LUAL_BUFFERSIZE, f);
        luaL_addsize(&b, nr);
    } while (nr == LUAL_BUFFERSIZE);
    luaL_pushresult(&b);
    return lua_tolstring(L, -1, len);
}


#ifdef __ANDROID__
#include <android/log.h>
#define LOG_TAG "lua"
#define LOGD(...) __android_log_print(ANDROID_LOG_INFO, LOG_TAG, __VA_ARGS__)
#endif

LUALIB_API int luaL_loadfilex (lua_State *L, const char *filename,
                               const char *mode) {
    LoadF lf;
    int status, readstatus;
    int c;
    int fnameindex = lua_gettop(L) + 1;  /* index of filename on the stack */
    if (filename == NULL) {
        lua_pushliteral(L, "=stdin");
        lf.f = stdin;
    }
    else {
        lua_pushfstring(L, "@%s", filename);
        lf.f = fopen(filename, "r");
        if (lf.f == NULL) return errfile(L, "open", fnameindex);
    }
    if (skipcomment(&lf, &c))  /* read initial portion */
        lf.buff[lf.n++] = '\n';  /* add line to correct line numbers */

    if (c == LUA_SIGNATURE[0] && filename) {  /* binary file? */
        lf.f = freopen(filename, "rb", lf.f);  /* reopen in binary mode */
        skipcomment(&lf, &c);  /* re-read initial portion */
    }
    if (c != EOF)
        lf.buff[lf.n++] = c;  /* 'c' is the first character of the stream */
    status = lua_load(L, getF, &lf, lua_tostring(L, -1), mode);
    readstatus = ferror(lf.f);
    if (filename) fclose(lf.f);  /* close file (even in case of errors) */
    if (readstatus) {
        lua_settop(L, fnameindex);  /* ignore results from 'lua_load' */
        return errfile(L, "read", fnameindex);
    }
    lua_remove(L, fnameindex);
    return status;
}


typedef struct LoadS {
  const char *s;
  size_t size;
} LoadS;


static const char *getS (lua_State *L, void *ud, size_t *size) {
  LoadS *ls = (LoadS *)ud;
  (void)L;  /* not used */
  if (ls->size == 0) return NULL;
  *size = ls->size;
  ls->size = 0;
  return ls->s;
}


LUALIB_API int luaL_loadbufferx (lua_State *L, const char *buff, size_t size,
                                 const char *name, const char *mode) {
  //LOGD("encrypt %d %s %x %s",size,name,buff[0],buff);
  LoadS ls;
  ls.s = buff;
  ls.size = size;
  return lua_load(L, getS, &ls, name, mode);
}


LUALIB_API int luaL_loadstring (lua_State *L, const char *s) {
  return luaL_loadbuffer(L, s, strlen(s), s);
}

/* }====================================================== */

LUALIB_API int luaL_getmetafield (lua_State *L, int obj, const char *event) {
  if (!lua_getmetatable(L, obj))  /* no metatable? */
    return LUA_TNIL;
  else {
    int tt;
    lua_pushstring(L, event);
    tt = lua_rawget(L, -2);
    if (tt == LUA_TNIL)  /* is metafield nil? */
      lua_pop(L, 2);  /* remove metatable and metafield */
    else
      lua_remove(L, -2);  /* remove only metatable */
    return tt;  /* return metafield type */
  }
}


LUALIB_API int luaL_callmeta (lua_State *L, int obj, const char *event) {
  obj = lua_absindex(L, obj);
  if (luaL_getmetafield(L, obj, event) == LUA_TNIL)  /* no metafield? */
    return 0;
  lua_pushvalue(L, obj);
  lua_call(L, 1, 1);
  return 1;
}


LUALIB_API lua_Integer luaL_len (lua_State *L, int idx) {
  lua_Integer l;
  int isnum;
  lua_len(L, idx);
  l = lua_tointegerx(L, -1, &isnum);
  if (!isnum)
    luaL_error(L, "对象长度不是一个整数");
  lua_pop(L, 1);  /* remove object */
  return l;
}


LUALIB_API const char *luaL_tolstring (lua_State *L, int idx, size_t *len) {
  if (!luaL_callmeta(L, idx, "__tostring")) {  /* no metafield? */
    switch (lua_type(L, idx)) {
      case LUA_TNUMBER: {
        if (lua_isinteger(L, idx))
          lua_pushfstring(L, "%I", lua_tointeger(L, idx));
        else
          lua_pushfstring(L, "%f", lua_tonumber(L, idx));
        break;
      }
      case LUA_TSTRING:
        lua_pushvalue(L, idx);
        break;
      case LUA_TBOOLEAN:
        lua_pushstring(L, (lua_toboolean(L, idx) ? "true" : "false"));
        break;
      case LUA_TNIL:
        lua_pushliteral(L, "nil");
        break;
      default:
        lua_pushfstring(L, "%s: %p", luaL_typename(L, idx),
                                            lua_topointer(L, idx));
        break;
    }
  }
  return lua_tolstring(L, -1, len);
}


/*
** {======================================================
** Compatibility with 5.1 module functions
** =======================================================
*/
#if defined(LUA_COMPAT_MODULE)
//mod by nirenr
LUALIB_API int luaL_typerror (lua_State *L, int narg, const char *tname) {
    return typeerror(L, narg, tname);
}

LUALIB_API const char *luaL_findtable (lua_State *L, int idx,
                                   const char *fname, int szhint) {
  const char *e;
  if (idx) lua_pushvalue(L, idx);
  do {
    e = strchr(fname, '.');
    if (e == NULL) e = fname + strlen(fname);
    lua_pushlstring(L, fname, e - fname);
    if (lua_rawget(L, -2) == LUA_TNIL) {  /* no such field? */
      lua_pop(L, 1);  /* remove this nil */
      lua_createtable(L, 0, (*e == '.' ? 1 : szhint)); /* new table for field */
      lua_pushlstring(L, fname, e - fname);
      lua_pushvalue(L, -2);
      lua_settable(L, -4);  /* set new table into field */
    }
    else if (!lua_istable(L, -1)) {  /* field has a non-table value? */
      lua_pop(L, 2);  /* remove table and value */
      return fname;  /* return problematic part of the name */
    }
    lua_remove(L, -2);  /* remove previous table */
    fname = e + 1;
  } while (*e == '.');
  return NULL;
}


/*
** Count number of elements in a luaL_Reg list.
*/
static int libsize (const luaL_Reg *l) {
  int size = 0;
  for (; l && l->name; l++) size++;
  return size;
}


/*
** Find or create a module table with a given name. The function
** first looks at the _LOADED table and, if that fails, try a
** global variable with that name. In any case, leaves on the stack
** the module table.
*/
//mod by nirenr
LUALIB_API void luaL_pushmodule (lua_State *L, const char *modname,
                                 int sizehint) {
  luaL_findtable(L, LUA_REGISTRYINDEX, "_LOADED", 1);  /* get _LOADED table */
  if (lua_getfield(L, -1, modname) != LUA_TTABLE) {  /* no _LOADED[modname]? */
    lua_pop(L, 1);  /* remove previous result */
    /* try global variable (and create one if it does not exist) */
    /*lua_pushglobaltable(L);
    if (luaL_findtable(L, 0, modname, sizehint) != NULL)
      luaL_error(L, "name conflict for module '%s'", modname);*/
	lua_newtable(L);
    lua_pushvalue(L, -1);
    lua_setfield(L, -3, modname);  /* _LOADED[modname] = new table */
  }
  lua_remove(L, -2);  /* remove _LOADED table */
}


LUALIB_API void luaL_openlib (lua_State *L, const char *libname,
                               const luaL_Reg *l, int nup) {
  luaL_checkversion(L);
  if (libname) {
    luaL_pushmodule(L, libname, libsize(l));  /* get/create library table */
    lua_insert(L, -(nup + 1));  /* move library table to below upvalues */
  }
  if (l)
    luaL_setfuncs(L, l, nup);
  else
    lua_pop(L, nup);  /* remove upvalues */
}

#endif
/* }====================================================== */

/*
** set functions from list 'l' into table at top - 'nup'; each
** function gets the 'nup' elements at the top as upvalues.
** Returns with only the table at the stack.
*/
LUALIB_API void luaL_setfuncs (lua_State *L, const luaL_Reg *l, int nup) {
  luaL_checkstack(L, nup, "too many upvalues");
  for (; l->name != NULL; l++) {  /* fill the table with given functions */
    int i;
    for (i = 0; i < nup; i++)  /* copy upvalues to the top */
      lua_pushvalue(L, -nup);
    lua_pushcclosure(L, l->func, nup);  /* closure with those upvalues */
    lua_setfield(L, -(nup + 2), l->name);
  }
  lua_pop(L, nup);  /* remove upvalues */
}


/*
** ensure that stack[idx][fname] has a table and push that table
** into the stack
*/
LUALIB_API int luaL_getsubtable (lua_State *L, int idx, const char *fname) {
  if (lua_getfield(L, idx, fname) == LUA_TTABLE)
    return 1;  /* table already there */
  else {
    lua_pop(L, 1);  /* remove previous result */
    idx = lua_absindex(L, idx);
    lua_newtable(L);
    lua_pushvalue(L, -1);  /* copy to be left at top */
    lua_setfield(L, idx, fname);  /* assign new table to field */
    return 0;  /* false, because did not find table there */
  }
}


/*
** Stripped-down 'require': After checking "loaded" table, calls 'openf'
** to open a module, registers the result in 'package.loaded' table and,
** if 'glb' is true, also registers the result in the global table.
** Leaves resulting module on the top.
*/
LUALIB_API void luaL_requiref (lua_State *L, const char *modname,
                               lua_CFunction openf, int glb) {
  luaL_getsubtable(L, LUA_REGISTRYINDEX, "_LOADED");
  lua_getfield(L, -1, modname);  /* _LOADED[modname] */
  if (!lua_toboolean(L, -1)) {  /* package not already loaded? */
    lua_pop(L, 1);  /* remove field */
    lua_pushcfunction(L, openf);
    lua_pushstring(L, modname);  /* argument to open function */
    lua_call(L, 1, 1);  /* call 'openf' to open module */
    lua_pushvalue(L, -1);  /* make copy of module (call result) */
    lua_setfield(L, -3, modname);  /* _LOADED[modname] = module */
  }
  lua_remove(L, -2);  /* remove _LOADED table */
  if (glb) {
    lua_pushvalue(L, -1);  /* copy of module */
    lua_setglobal(L, modname);  /* _G[modname] = module */
  }
}


LUALIB_API const char *luaL_gsub (lua_State *L, const char *s, const char *p,
                                                               const char *r) {
  const char *wild;
  size_t l = strlen(p);
  luaL_Buffer b;
  luaL_buffinit(L, &b);
  while ((wild = strstr(s, p)) != NULL) {
    luaL_addlstring(&b, s, wild - s);  /* push prefix */
    luaL_addstring(&b, r);  /* push replacement in place of pattern */
    s = wild + l;  /* continue after 'p' */
  }
  luaL_addstring(&b, s);  /* push last suffix */
  luaL_pushresult(&b);
  return lua_tostring(L, -1);
}


static void *l_alloc (void *ud, void *ptr, size_t osize, size_t nsize) {
  (void)ud; (void)osize;  /* not used */
  if (nsize == 0) {
    free(ptr);
    return NULL;
  }
  else
    return realloc(ptr, nsize);
}


static int panic (lua_State *L) {
  lua_writestringerror("PANIC: unprotected error in call to Lua API (%s)\n",
                        lua_tostring(L, -1));
  return 0;  /* return to Lua to abort */
}


LUALIB_API lua_State *luaL_newstate (void) {
  lua_State *L = lua_newstate(l_alloc, NULL);
  if (L) lua_atpanic(L, &panic);
  return L;
}


LUALIB_API void luaL_checkversion_ (lua_State *L, lua_Number ver, size_t sz) {
  const lua_Number *v = lua_version(L);
  if (sz != LUAL_NUMSIZES)  /* check numeric types */
    luaL_error(L, "核心和库的数值类型不兼容");
  if (v != lua_version(NULL))
    luaL_error(L, "检测到多个 Lua VM");
  else if (*v != ver)
    luaL_error(L, "版本不匹配：应用程序需要 %f，Lua 核心提供 %f",
                  ver, *v);
}
