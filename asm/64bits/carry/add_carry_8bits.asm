section .text
global add_carry_8bits


add_carry_8bits:

  mov al, dil
  mov bl, sil
  add al, bl
  jc carry
  xor rax, rax  ; no carry from addition
  ret
carry:
  mov rax, 1
  ret
