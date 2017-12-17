#include <stdio.h>
#include <assert.h>

unsigned pwr2k (unsigned k) {
    return 1U << k;
}

unsigned div_by_2k (unsigned x, unsigned k) {
    return x >> k;
}

unsigned div_by_2k_check (unsigned x, unsigned k) {
    return x / pwr2k(k);
}

int sdiv_by_2k (int x, unsigned k) {
    return (x < 0 ? x + (1 << k) - 1 : x) >> k; 
}

int sdiv_by_2k_check (int x, unsigned k) {
    return x / (int) pwr2k(k);
}

int main() {
    unsigned k;
    unsigned x;
    int sx;
    unsigned step = 11371U;
    int sstep = (int) step;
    unsigned N = 0U;

    for(k = 0; k < 32; ++k) {
        for(x = 0; x < x + step; x += step) {
            unsigned u1 = div_by_2k(x,k);
            unsigned u2 = div_by_2k_check(x,k);
            N +=1;
            assert (u1 == u2);
        }
    }

    for(k = 0; k < 31; ++k) {
        for(sx = -0x80000000; sx < sx + sstep; sx += sstep) { 
            int s1 = sdiv_by_2k(sx,k);
            int s2 = sdiv_by_2k_check(sx,k);
            N +=1;
            assert (s1 == s2);
        }
    }

    printf("Number of checks carried out: %u\n", N);


   return 0;
} 

