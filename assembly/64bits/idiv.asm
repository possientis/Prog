        segment .data
x       dq  512
y       dq  3
quot    dq  0
rem     dq  0

        segment .text
        global _start
_start:

        mov   rax, [x]    
        mov   rdx, 0      ; rdx:rax == rax
        idiv  qword [y]   ; divide by y
        mov   [quot], rax ; store the quotient
        mov   [rem], rdx  ; store the remainder

        ret
