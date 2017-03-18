section .bss
        Buff resb 1   ; only one byte in buffer

section .data

section .text
        global _start

_start:

        nop ; debugger happy

Read:   mov eax,  3   ; sys_read call 32 bits ABI
        mov ebx,  0   ; stdin
        mov ecx, Buff ; buffer to read to
        mov edx,  1   ; reading 1 bye only
        int 0x80      ; call sys_read

        cmp eax,  0   ; sys_read return value
        je  Exit      ; if 0 (EOF) exit

        cmp byte [Buff], 0x61 ; 'a'
        jb  Write     ; if below, not a lower case char
        cmp byte [Buff], 0x7a ; 'z'
        ja  Write     ; if above, not a lower case char
        sub byte [Buff], 0x20 ; toUpper

Write:  mov eax,  4   ; sys_write call 32 bits ABI
        mov ebx,  1   ; stdout
        mov ecx,  Buff
        mov edx,  1
        int 0x80
        jmp Read

Exit:
        mov eax,  1   ; sys_exit call 32 bits ABI
        mov ebx,  0   ; return status
        int 0x80


