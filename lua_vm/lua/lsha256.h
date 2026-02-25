#ifndef lsha256_h
#define lsha256_h

#include <stddef.h>
#include <stdint.h>

typedef struct {
    uint32_t state[8];
    uint64_t count;
    uint8_t buffer[64];
} SHA256_CTX;

void l_sha256_init(SHA256_CTX *ctx);
void l_sha256_update(SHA256_CTX *ctx, const uint8_t *data, size_t len);
void l_sha256_final(SHA256_CTX *ctx, uint8_t digest[32]);

#endif
