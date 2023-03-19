        segment .data
a       dq  34
b       dq  45

        segment .text
        global _start

_start:
        mov rax, [a]
        mov rbx, [b]
        cmp rax, rbx
        jge in_order
        mov [a], rbx
        mov [b], rax 
in_order:
        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
