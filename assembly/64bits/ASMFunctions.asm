%macro print 1    ; 1 argument
  mov rdi, %1
  mov rsi, [rbp-%1*8]
  call printArgument
%endmacro
 
global longASMFunction
extern printf

section .data
format  db "x%d = %lx",10,0

section .text


longASMFunction:
  ; prologue
  push rbp
  mov  rbp, rsp
  sub  rsp, 48

  ; saving arguments
  mov [rbp-8], rdi
  mov [rbp-16], rsi
  mov [rbp-24], rdx
  mov [rbp-32], rcx
  mov [rbp-40], r8
  mov [rbp-48], r9

  print 1
  print 2
  print 3
  print 4
  print 5
  print 6

  ; return value
  mov rax, 0x1234567812345678
  
  ; epilogue
  leave
  ret  


printArgument:  ; printf(format, i, value)
  mov rdx, rsi    ; second argument of print becomes third argument of printf
  mov rsi, rdi    ; first argument of print becomes second argument of printf
  mov rdi, format ; first argument of printf
  xor rax, rax
  call printf
  ret

 
  

