; illustrate the use of string instructions
section .data
  EOL       equ 10    ; 0x0a
  FILLCHR   equ 32    ; 0x20
  DASHCHR   equ 45    ; 0x2d
  STRTROW   equ 2     ; row where graph begins

  ; table of byte-length numbers
  Dataset   db  9,71,17,52,55,18,29,36,18,68,77,63,58,44,0

  Message   db  "Data current as of 26/04/2017"
  MSGLEN    equ $-Message

  ; terminal escape sequence to clear screen and position cursor (1,1)
  ClrHome   db  27,"[2J",27,"[01;01H"
  CLRLEN    equ $-ClrHome

section .bss

  COLS      equ 81            ; line length + 1 char for EOL
  ROWS      equ 25            ; Number of lines in display
  VidBuff   resb  COLS*ROWS   ; video buffer

section .text
global _start

%macro ClearTerminal 0        ; macro takes 0 argument
  push  rax
  push  rdi
  push  rsi
  push  rdx
  mov   rax, 1                ; sys_write 64 bits
  mov   rdi, 1                ; stdout
  mov   rsi, ClrHome          ; escape sequence to be sent to stdout
  mov   rdx, CLRLEN           ; length to write
  syscall
  pop   rdx
  pop   rsi
  pop   rdi
  pop   rax
%endmacro

; sends the video buffer to Linux terminal via sys_write
Show:
  push  rax
  push  rdi
  push  rsi
  push  rdx
  mov   rax, 1                ; sys_write 64 bits
  mov   rdi, 1                ; stdout
  mov   rsi, VidBuff          ; video buffer
  mov   rdx, COLS*ROWS        ; length of buffer
  syscall
  pop   rdx
  pop   rsi
  pop   rdi
  pop   rax
  ret

; fills video bufferwith predefined char character (FILLCHR) and
; then places an EOL character at the end of every line
ClrVid:
  push  rax
  push  rdi
  push  rcx
  cld                         ; clear DF (direction flag), counting up memory
  mov   al, FILLCHR
  mov   rdi, VidBuff
  mov   rcx, COLS*ROWS        ; stosb alone as semantics: *rdi++ = al
  rep   stosb                 ; do { *rdi++ = al; rcx--; } while (rcx > 0);
  ; need to insert EOL's
  mov   rdi, VidBuff
  dec   rdi                   ; index -1  
  mov   rcx, ROWS
ptEOL:
  add   rdi, COLS
  mov   byte [rdi], EOL
  loop  ptEOL
  pop   rcx
  pop   rdi
  pop   rax
  ret

; writes string to video buffer at position X,Y (1-based)
; IN: address of string in RSI
;     X position (col # 1-based) in RBX
;     Y position (row # 1-based) in RAX
;     Length of the string in RCX
WrtLn:
  push  rax
  push  rbx
  push  rcx
  push  rdi
  cld                         ; clear DF (direction flag), counting up memory
  mov   rdi, VidBuff
  dec   rax                   ; now 0-based, for address calculation
  dec   rbx                   ; now 0-based
  mov   ah, COLS              ; move screen width to AH
  mul   ah                    ; ax = al*ah 
  add   rdi, rax              ; add Y offset into VidBuff to rdi
  add   rdi, rbx              ; add X offset into VidBuff to rdi
  rep   movsb                 ; *rdi++ = *rsi++
  pop   rdi                   ; movsb, movsw, movsd, movsq
  pop   rcx
  pop   rbx
  pop   rax
  ret

; generates a horizontal bar at X,Y in video buffer
; IN: 
;     X position (col # 1-based) in RBX
;     Y position (row # 1-based) in RAX
;     Length of the bar in chars in RCX
; 
WrtDsh:
  push  rax
  push  rbx
  push  rcx
  push  rdi
  cld
  mov   rdi, VidBuff
  dec   rax
  dec   rbx
  mov   ah, COLS
  mul   ah
  add   rdi, rax
  add   rdi, rbx
  mov   al, DASHCHR  
  rep   stosb
  pop   rdi
  pop   rcx
  pop   rbx
  pop   rax
  ret
  
; generates a "1234567890"-style ruler at X,Y in video buffer
; IN: 
;     X position (col # 1-based) in RBX
;     Y position (row # 1-based) in RAX
;     Length of the ruler in chars in RCX
; 
Ruler:
  push  rax
  push  rbx
  push  rcx
  push  rdi
 
  mov   rdi, VidBuff
  dec   rax
  dec   rbx 
  mov   ah, COLS
  mul   ah
  add   rdi, rax
  add   rdi, rbx
  mov   al, '1'   ; start ruler with digit '1'
DoChar:
  stosb           ; *rdi++ = al;
  add   al, 1     ; bump character value by 1
  cmp   al,'9'
  jbe   DoLoop
  mov   al, '0'
DoLoop:
  loop  DoChar    ; dec rcx; jnz DoChar

  pop   rdi
  pop   rcx
  pop   rbx
  pop   rax
  ret
  
_start

  ClearTerminal     ; macro call 
  call  ClrVid      ; function call

  ; display top ruler
  mov   rax, 1
  mov   rbx, 1
  mov   rcx, COLS-1
  call  Ruler
  
  ; loop through dataset and graph data
  mov   rsi, Dataset
  mov   rbx, 1        ; X = 1
  mov   rbp, 0        ; index = 0
.blast
  mov   rax, rbp
  add   rax, STRTROW
  mov   cl, byte [rsi+rbp]
  cmp   rcx, 0
  je    .rule2        ; if 0 from dataset -> done
  call  WrtDsh
  inc   rbp           ; index++
  jmp   .blast
  
  ; display bottom ruler
.rule2
  mov   rax, rbp      ; rax = index 
  add   rax, STRTROW
  mov   rbx, 1
  mov   rcx, COLS-1
  call  Ruler

  ;informative message on the last line
  mov   rsi, Message 
  mov   rcx, MSGLEN
  mov   rbx, COLS
  sub   rbx, rcx
  shr   rbx, 1
  mov   rax, 24       ; last line
  call  WrtLn

  ; display video buffer
  call Show 

  mov   rax, 60
  mov   rdi, 0
  syscall



