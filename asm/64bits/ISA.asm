        section .data
a       dq      0x1234567890123456

        section .text
        global _start

_start:
        ; MOV
        mov rax, rbx      ; register to register
        mov rax, [a]      ; memory to register
        mov rax, 2        ; immediate to register


        ; exiting
        mov   rax, 0x3c
        mov   rdi, 0
        syscall
