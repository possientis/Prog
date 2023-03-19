        section .text
        global _start
        extern _exit

_start:
        mov al , 60
        mov dil, 42
        syscall
