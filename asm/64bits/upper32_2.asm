section .bss

BUFFLEN equ 1024
Buff:   resb BUFFLEN

section .data

section .text

global  _start

_start:

        nop               ; debugger happy

Read:   mov eax,  3       ; sys_read 32 bits ABI
        mov ebx,  0       ; stdin
        mov ecx,  Buff    ; buffer for read
        mov edx,  BUFFLEN ; number of bytes to read
        int 0x80 
        mov esi,  eax     ; saving return value
        cmp eax,  0       ; EOF?
        je  Exit

        mov ecx,  esi     ; number of bytes in ecx  
        mov ebp,  Buff    ; buffer address into ebp
        dec ebp           ; so that ebp+ecx point to final byte

Scan:
        cmp byte [ebp+ecx], 0x61  ; 'a'
        jb  Next          ; not a lower case char
        cmp byte [ebp+ecx], 0x7a  ; 'z'
        ja  Next          ; not a lower case char
        sub byte [ebp+ecx], 0x20  ; toUpper
        
Next:   dec ecx
        jnz Scan

        mov eax,  4       ; sys_write 32 bits ABI
        mov ebx,  1       ; stdout
        mov ecx,  Buff    ; buffer for write
        mov edx,  esi     ; writing as many as were read
        int 0x80
        jmp Read

Exit:
        mov eax,  1       ; sys_exit 32 bits ABI
        mov ebx,  0       ; return value
        int 0x80
