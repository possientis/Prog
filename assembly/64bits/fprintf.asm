section .data
  Message db "Hello world!",0x0a,0

section .text
  global main
  extern fprintf
  extern stdout

main:
  mov rdi, [stdout] ; stdin, stderr
  mov rsi, Message
  xor rax, rax
  call fprintf

  xor rax, rax
  ret 
