        section .text
        global _start

_start:
        xor   eax, eax
        xor   ebx, ebx
        xor   ecx, ecx
        cdq             ; what is that?
        mov   al, 0xa4  ; probably some 2 bits system call
        int   0x80      ; gdb shows system call failing (returns -1)
        push  0xb
        pop   rax
        push  rcx
        push  0x68732f2f
        push  0x6e69622f
        mov   ebx, esp
        push  rcx
        mov   edx, esp
        push  rbx
        mov   ecx, esp
        int   0x80 
        mov   rax, 0x3c
        mov   rdi, 0
        syscall
