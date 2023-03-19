%include "macro.asm"  ; extension need not be 'asm'

%define num 15  ; one line macro here

section .text
global _start

_start:
  exitcode num


