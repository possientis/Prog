section .text
global _start
_start:

  hlt           ; segmentation fault

  mov rax, 60
  mov rdi, 0
  syscall


