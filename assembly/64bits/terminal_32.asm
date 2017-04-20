section     .data
SCRWIDTH:   equ 80                  ; by default we assume 80 chars wide
PosTerm:    db 27,"[01;01H"         ; <ESC>[<Y>;<X>H
POSLEN:     equ $-PosTerm           ; Length of Term position string 
ClearTerm:  db 27,"[2J"             ; <ESC>[2J
CLEARLEN:   equ $-ClearTerm         ; Length of Term clearing string
Msg:        db "Hello, world!"      ; message
MSGLEN:     equ $-Msg               ; Length of message
Prompt:     db "Press <Enter>: "    ; User prompt
PROMPTLEN:  equ $-Prompt            ; length of user prompt

; This table gives us pairs of ASCII digits from 0-80. Rather than
; calculate ASCII digits to insert in the terminal control string,
; we look them up in the table and read back two digits at once to
; a 16-bit register like DX, which we then poke into the terminal
; control string PosTerm at the appropriate place. See GotoXY.
; If you intend to work on a larger console than 80 X 80, you must
; add additional ASCII digit encoding to the end of Digits. Keep in
; mind that the code shown here will only work up to 99 X 99.

Digits:     db "0001020304050607080910111213141516171819"
            db "2021222324252627282930313233343536373839"
            db "4041424344454647484950515253545556575859"
            db "606162636465666768697071727374757677787980"

section     .text
ClrScr:
            push  rax               ; save pertinent registers
            push  rbx        
            push  rcx
            push  rdx
            mov   rcx, ClearTerm    ; pass offset of terminal control string
            mov   rdx, CLEARLEN     ; pass the length of terminal control string
            call  WriteStr          ; send control string to console
            pop   rdx
            pop   rcx
            pop   rbx
            pop   rax
            ret                     ; go home

; IN: X in AH, Y in AL
GotoXY:
            pushaq                  ; save caller's registers 
            xor   rbx, rbx          ; zero rbx
            xor   rcx, rcx   
; poke the Y digits
            mov   bl, al
            mov   cx, word [Digits+rbx*2]
            mov   word [PosTerm+2], cx
; poke the X digits
            mov   bl, ah
            mov   cx, word [Digits+rbx*2]
            mov   word [PosTerm+5] , cx
      
            mov   rcx, PosTerm
            mov   rdx, POSLEN
            call  WriteStr

            popaq
            ret

; send a string centered to an 80-char wide Linux console
; IN: Y value in AL, string address in RCX, string length in RDX
WriteCtr:
            push  rbx
            xor   rbx, rbx
            mov   bl, SCRWIDTH 
            sub   bl, dl            ; width - length
            shr   bl, 1             ; divide by two
            mov   ah, bl            ; GotoXY requires X in AH
            call  GotoXY            ; position cursor for display
            call  WriteStr
            pop   rbx
            ret 
            
WriteStr: ; TODO

