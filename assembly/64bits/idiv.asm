        segment .data
x       dq  512
y       dq  3
quot    dq  0
rem     dq  0

        segment .text
        global _start
_start:

        mov   rax, [x]    
        mov   rdx, 0      ; idiv divides 128 bits rdx:rax
        idiv  qword [y]   ; divide by y
        mov   [quot], rax ; store the quotient
        mov   [rem], rdx  ; store the remainder

        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
