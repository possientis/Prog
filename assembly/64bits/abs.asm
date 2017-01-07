        segment .data
a       dq  -45
b       dq 100

        segment .text
        global _start

_start:

        mov   rax, [a]  ; load a
        mov   rbx, rax  ; make copy
        neg   rax       ; negate a
        cmovl rax, rbx  ; replace if negative
                        ; rax should be abs(a)

        mov   rax, [b]
        mov   rbx, rax
        neg   rax
        cmovl rax, rbx  ; rax should be abs(b)

        ret
