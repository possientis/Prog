        section .text
        global _start

_start:
        mov rax, 0x40
        mov rax, 40h

        mov rax, 60
        mov rdi, 0
        syscall
