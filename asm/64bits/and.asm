        segment .data
        
        segment .text
        global _start

_start:

        mov   rax, 0x1234567812345678
        mov   rbx, rax
        and   rbx, 0xf  ; rbx = 0x8
        mov   rdx, 0    ; preparing to divide
        mov   rcx, 16   ; by 16
        idiv  rcx       ; rax = 0x0123456781234567
        and   rax, 0xf  ; rax = 0x7, rdx = 0x8

        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
