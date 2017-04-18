global _start
_start:
call mark_below
db "Hello, world!", 0x0a,0x0d

mark_below:
pop rsi
mov rax, 1
mov rdi, 1
mov rdx, 15
syscall

mov rax, 60
mov rdi, 0
syscall
