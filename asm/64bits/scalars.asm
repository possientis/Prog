        segment .data
a       dd      -5.678    ; 32 bits
b       dq       4.678    ; 64 bits

        segment .bss
c       dd      0
d       dq      0

        segment .text
        global main

main:
                            ; xmm registers are 128 bits
                            ; ymm registers are 256 bits
        movss   xmm0, [a]   ; move 32 bits value into xmm0
        movsd   xmm1, [b]   ; move 64 bits value into xmm1
        movss   xmm2, xmm0  
        movsd   xmm15, xmm1 ; xmm0, ..., xmm15
        movss   [c], xmm0
        movsd   [d], xmm1

        ret
