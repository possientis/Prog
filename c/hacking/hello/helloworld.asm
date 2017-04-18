section .data
msg     db    "Hello, world!",0x0a

section .text
global _start

_start:
; SYSCALL: write(1,msg,14)
mov rax,1
mov rdi,1
mov rsi, msg
mov rdx, 14
syscall

;SYSCALL: exit(0)
mov rax, 60
mov rdi, 0
syscall
