        segment .data
a       dq  -45
b       dd  -10
c       dw  -20
d       db  -30 
e       dq  0


        segment .text
        global  _start
_start:
        mov     rax, [a]
        movsxd  rbx, dword [b]
        movsx   rcx, word [c]
        movsx   rdx, byte [d]
        add     rax, rbx
        add     rax, rcx
        add     rax, rdx
        mov     [e], rax
        xor     rax, rax
        ret
