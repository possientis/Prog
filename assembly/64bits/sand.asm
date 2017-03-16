section .data

wordstring: dw 'CQ'
doublestring: dd 'Stop'
Len  equ $-wordstring


section .text
global _start

_start:

  mov ax, [wordstring]
  mov edx, [doublestring]
  mov bl, Len

  mov rax, 1
  xor rbx, rbx
  int 0x80

;  mov rax, 60
;  mov rdi, 0
;  syscall
