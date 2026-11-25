#include <stdint.h>

/* FIPS 180-4 section 6.2.2. Return the new working word a. */
uint32_t sha256_round_a(uint32_t a, uint32_t b, uint32_t c,
                        uint32_t e, uint32_t f, uint32_t g, uint32_t h,
                        uint32_t k, uint32_t w) {
    uint32_t sigma0 = __builtin_rotateright32(a, 2) ^
                      __builtin_rotateright32(a, 13) ^
                      __builtin_rotateright32(a, 22);
    uint32_t sigma1 = __builtin_rotateright32(e, 6) ^
                      __builtin_rotateright32(e, 11) ^
                      __builtin_rotateright32(e, 25);
    uint32_t choose = g ^ (e & (f ^ g));
    uint32_t majority = (a & b) | (c & (a | b));
    return (h + sigma1 + choose + k + w) + (sigma0 + majority);
}
