section .text
global _start
  

_start:
  
  mov al, 255
  mov bl, 0 
  sub al, bl



  mov rax, 60
  mov rdi, 0
  syscall
