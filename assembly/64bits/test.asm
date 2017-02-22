        segment .text
        global _start

_start:
        inc   eax
end:
        mov   rax, 60     ; sys call number
        mov   rdi, 0      ; returned status code
        syscall
