section .bss
        Buff resb 1   ; only one byte in buffer

section .data

section .text
        global _start

_start:

        nop ; debugger happy

Read:   mov rax,  0   ; sys_read call 64 bits ABI
        mov rdi,  0   ; stdin
        mov rsi, Buff ; buffer to read to
        mov rdx,  1   ; reading 1 bye only
        syscall       ; call sys_read

        cmp rax,  0   ; sys_read return value
        je  Exit      ; if 0 (EOF) exit

        cmp byte [Buff], 0x61 ; 'a'
        jb  Write     ; if below, not a lower case char
        cmp byte [Buff], 0x7a ; 'z'
        ja  Write     ; if above, not a lower case char
        sub byte [Buff], 0x20 ; toUpper

Write:  mov rax,  1   ; sys_write call 64 bits ABI
        mov rdi,  1   ; stdout
        mov rsi,  Buff
        mov rdx,  1
        syscall
        jmp Read

Exit:
        mov rax,  60  ; sys_exit call 64 bits ABI
        mov rdi,  0   ; return status
        syscall


