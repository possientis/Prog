        segment .data
        segment .text
        global _start
_start:
        mov rax, 0x1000
        or  rax, 1        ; make he number odd
        or  rax, 0xff00   ; set bits 15-8

        ret
