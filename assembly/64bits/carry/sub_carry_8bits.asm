section .text
global sub_carry_8bits


sub_carry_8bits:

  mov al, dil
  mov bl, sil
  sub al, bl
  jc carry
  xor rax, rax  ; no carry from addition
  ret
carry:
  mov rax, 1
  ret
