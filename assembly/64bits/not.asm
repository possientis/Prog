        segment .data

        segment .text
        global _start

_start:
        mov rax, 0
        not rax       ; rax = 0xffffffffffffffff
        mov rdx, 0    ; preparing for divide
        mov rbx, 15   ; will divide by 15 (0xf)
        div rbx       ; unsigned divide, rax = 0x1111111111111111
        not rax       ; rax = 0xeeeeeeeeeeeeeeee

        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
