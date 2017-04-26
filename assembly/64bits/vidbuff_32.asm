section .data
  EOL       equ 10    ; 0x0a
  FILLCHR   equ 32    ; 0x20
  DASHCHR   equ 45    ; 0x2d
  STARTROW  equ 2     ; row where graph begins

  ; table of byte-length numbers
  Dataset   db  9,71,17,52,55,18,29,36,18,68,77,63,58,44,0

  Message   db  "Data current as of 26/04/2017"
  MSGLEN    equ $-Message

  ; terminal escape sequence to clear screen and position cursor (1,1)
  ClrHome   db  27,"[2J",27,"[01;01H"
  CLRLEN    equ $-ClrHome

section .bss

  COLS      equ 81          ; line length + 1 char for EOL
  ROWS      equ 25          ; Number of lines in display
  VidBuff   resb  COLS*ROWS ; video buffer

section .text
global _start

%macro ClearTerminal 0      ; macro takes 0 argument
  pushaq                    ; save all registers
  mov rax, 1                ; sys_write 64 bits
  mov rdi, 1                ; stdout
  mov rsi, ClrHome          ; escape sequence to be sent to stdout
  mov rdx, CLRLEN           ; length to write
  syscall
  popaq
%endmacro

; sends the video buffer to Linux terminal via sys_write
Show:
  pushaq
  mov rax, 1                ; sys_write 64 bits
  mov rdi, 1                ; stdout
  mov rsi, VidBuff          ; video buffer
  mov rdx, COLS*ROWS        ; length of buffer
  syscall
  popaq
  ret


_start

  ClearTerminal

  mov rax, 60
  mov rdi, 0
  syscall



