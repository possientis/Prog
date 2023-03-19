section .bss
        BUFFLEN equ 16      ; we read the file 16 bytes at a time
        Buff: resb BUFFLEN  ; text buffer

section .data
        HexStr: db " 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00",10
        HEXLEN equ $-HexStr

        Digits: db "0123456789abcdef"

section .text
global _start

_start:

        nop     ; debugger happy

Read:
        mov eax,  3       ; sys_read for 32 bits ABI
        mov ebx,  0       ; stdin
        mov ecx,  Buff    ; read buffer
        mov edx,  BUFFLEN ; number of bytes to be read per pass
        int 0x80
        mov ebp, eax      ; save return value
        cmp eax, 0        ; EOF?
        je  Exit          

        mov esi,  Buff
        mov edi,  HexStr
        xor ecx,  ecx

Scan:
        xor eax,  eax

        mov edx,  ecx
        shl edx,  1  
        add edx,  ecx     ; edx = 3 * ecx  

        mov al,   byte [esi+ecx]      ; take byte from read buffer
        mov ebx,  eax                 ; duplicate for second nimble

        and al,  0x0f                 ; keep low nibble
        mov al,   byte [Digits+eax]   ; get corresponding hex digit
        mov byte  [HexStr+edx+2], al  ; write to output string

        shr bl,   4                   ; align high nibble
        and ebx,  0xf                 ; mask out everything else
        mov bl,   byte [Digits+ebx]   ; get corresponding hex digit
        mov byte  [HexStr+edx+1], bl  ; write to output string

        inc ecx
        cmp ecx, ebp
        jb Scan


        mov eax,  4
        mov ebx,  1
        mov ecx,  HexStr
        mov edx,  HEXLEN
        int 0x80
        jmp Read

Exit:
        mov eax,  1
        mov ebx,  0
        int 0x80

        
