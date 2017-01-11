        segment .data
a       dq  -4.758
b       dd  2.678

        segment .text
        global _start

_start:

        mov rax, [a]
        mov rbx, [b]  ; check ebx

        ret
