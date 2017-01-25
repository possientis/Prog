        segment .data
        segment .text
        global _start

_start:

        mov rax, 0x12345678
        shr rax, 8          ; I want bits 8-15
        and rax, 0xff       ; rax = 0x56
        mov rax, 0x12345678 ; I want to replace bits 8-15
        mov rdx, 0xaa       ; rdx holds replacement field
        mov rbx, 0xff       ; I need an 8 bit mask
        shl rbx, 8          ; shift mask to align at bit 8
        not rbx             ; rbx is the inverted mask
        and rax, rbx        ; now bits 8-15 are all 0
        shl rdx, 8          ; shift the new bits to align
        or  rax, rdx        ; rax = 0x1234aa78

        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
