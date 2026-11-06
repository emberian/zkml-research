/* Keccak-f[1600], plain 64-bit form (checked against hashlib.shake_256 by check_encode.py) */
#pragma once
#include <stdint.h>
#include <string.h>
static const uint64_t KRC[24] = {
 0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,0x8000000080008000ULL,
 0x000000000000808bULL,0x0000000080000001ULL,0x8000000080008081ULL,0x8000000000008009ULL,
 0x000000000000008aULL,0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,
 0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,
 0x8000000000008002ULL,0x8000000000000080ULL,0x000000000000800aULL,0x800000008000000aULL,
 0x8000000080008081ULL,0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL};
#define ROL(x,n) (((x)<<(n))|((x)>>(64-(n))))
static void keccakf(uint64_t s[25]) {
    static const int r[25] = {0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14};
    for (int rd = 0; rd < 24; rd++) {
        uint64_t C[5], D[5], B[25];
        for (int x = 0; x < 5; x++) C[x] = s[x]^s[x+5]^s[x+10]^s[x+15]^s[x+20];
        for (int x = 0; x < 5; x++) D[x] = C[(x+4)%5] ^ ROL(C[(x+1)%5],1);
        for (int i = 0; i < 25; i++) s[i] ^= D[i%5];
        for (int x = 0; x < 5; x++) for (int y = 0; y < 5; y++) {
            int i = x + 5*y; uint64_t v = s[i]; int n = r[i];
            B[y + 5*((2*x+3*y)%5)] = n ? ROL(v,n) : v;
        }
        for (int x = 0; x < 5; x++) for (int y = 0; y < 5; y++)
            s[x+5*y] = B[x+5*y] ^ ((~B[(x+1)%5+5*y]) & B[(x+2)%5+5*y]);
        s[0] ^= KRC[rd];
    }
}
/* SHAKE256 / cSHAKE256-shaped sponge: rate 136, domain byte ds (0x1f SHAKE, 0x04 cSHAKE),
 * optional precomputed midstate (the customization block, absorbed once). Returns perms used. */
static long sponge256(const uint64_t *mid, uint8_t ds, const uint8_t *in, size_t n, uint8_t *out, size_t outn) {
    uint64_t s[25]; long perms = 0;
    if (mid) memcpy(s, mid, sizeof s); else memset(s, 0, sizeof s);
    uint8_t *sb = (uint8_t *)s;
    while (n >= 136) { for (int i = 0; i < 136; i++) sb[i] ^= in[i]; keccakf(s); perms++; in += 136; n -= 136; }
    for (size_t i = 0; i < n; i++) sb[i] ^= in[i];
    sb[n] ^= ds; sb[135] ^= 0x80; keccakf(s); perms++;
    while (outn) { size_t c = outn < 136 ? outn : 136; memcpy(out, sb, c); out += c; outn -= c; if (outn) { keccakf(s); perms++; } }
    return perms;
}
