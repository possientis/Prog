        segment .data
        segment .text
        global _start
_start:
        mov rax, 0x1234567812345678
        xor eax, eax    ; set to 0
        mov rax, 0x1234
        xor rax, 0xf    ; change to 0x123b

        ret
        
