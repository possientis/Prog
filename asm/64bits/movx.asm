section .data
a   db  0xaa
b   dw  0xbbbb
c   dd  0xcccccccc
d   dq  0xdddddddddddddddd

section .text
global _start

; this is all about 'move extend', i.e. moving a source
; operand into a destination of bigger size. As the data
; being moved potentially refer to signed integers, the
; question arises as to how the extension is carried out:
; do we 'zero extend' ? if yes, use movzx
; do we 'sign extend' ? if yes, use movsx
_start:
 
  mov   bl, 0xbb
  mov   cx, 0xcccc

; 8 bits source

  ; zero extension
  movzx ax,  byte [a]
  movzx eax, byte [a]
  movzx rax, byte [a]

  movzx ax,  bl
  movzx eax, bl
  movzx rax, bl

  ; sign extension
  movsx ax,  byte [a]
  movsx eax, byte [a]
  movsx rax, byte [a]

  movsx ax,  bl
  movsx eax, bl
  movsx rax, bl

; 16 bits source

  ; zero extension
  movzx eax, word [b]
  movzx rax, word [b]
  
  movzx eax, cx
  movzx rax, cx

  ; sign extension
  movsx eax, word [b]
  movsx rax, word [b]
  
  movsx eax, cx
  movsx rax, cx

; 32 bits source
  movzx rax, word [c] ; hmmmmm

; exit 0
  mov rax, 60 
  mov rdi, 0
  syscall
  
