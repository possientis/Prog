; This shellcode is no good, as it contains null bytes
        section .text
        global _start
_start:
        mov   rax, 1          ; sys_write
        mov   rdi, 1          ; stdout
        lea   rsi, [rip+0x19] ; buffer in code segment below
        mov   rdx, 22         ; size
        syscall

        mov   rax, 60       ; exit
        mov   rdi, 0        ; exit 0
        syscall
        db  0x73,0x68,0x65,0x6c,0x6c,0x20,0x63,0x6f
        db  0x64,0x65,0x20,0x69,0x73,0x20,0x72,0x75
        db  0x6e,0x6e,0x69,0x6e,0x67,0x0a
