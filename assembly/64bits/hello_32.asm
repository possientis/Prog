        segment .data
hello:  db "Hello world intel!", 0x0a

        segment .text
        global _start

_start:

        ; this is 32 bit code, still works under 64 bits
        mov   eax, 4        ; sys_write for 32 bits
        mov   ebx, 1        ; stdout
        lea   ecx, [hello]  ; buffer
        mov   edx, 19       ; size
        int   0x80          ; syscall for 32 bits

        ; this is 64 bit code
        mov   rax, 60       ; exit
        mov   rdi, 0        ; return value
        syscall
