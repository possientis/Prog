section .bss

BUFFLEN equ 1024
Buff:   resb BUFFLEN

section .data

section .text

global  _start

_start:

        nop               ; debugger happy

Read:   mov rax,  0       ; sys_read 64 bits ABI
        mov rdi,  0       ; stdin
        mov rsi,  Buff    ; buffer for read
        mov rdx,  BUFFLEN ; number of bytes to read
        syscall 

        mov rsi,  rax     ; saving return value
        cmp rax,  0       ; EOF?
        je  Exit

        mov rcx,  rsi     ; number of bytes in ecx  
        mov rbp,  Buff    ; buffer address into ebp
        dec rbp           ; so that rbp+rcx point to final byte

Scan:
        cmp byte [rbp+rcx], 0x61  ; 'a'
        jb  Next          ; not a lower case char
        cmp byte [rbp+rcx], 0x7a  ; 'z'
        ja  Next          ; not a lower case char
        sub byte [rbp+rcx], 0x20  ; toUpper
        
Next:   dec rcx
        jnz Scan

        mov rax,  1       ; sys_write 64 bits ABI
        mov rdi,  1       ; stdout
        mov rsi,  Buff    ; buffer for write
        mov rdx,  rsi     ; writing as many as were read
        syscall
        jmp Read

Exit:
        mov rax,  60      ; sys_exit 64 bits ABI
        mov rdi,  0       ; return value
        syscall

