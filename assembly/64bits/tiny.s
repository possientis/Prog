        .section .text
        .global _start
        .extern _exit

_start:
        movb  $60, %al
        movb  $42, %dil
        syscall
