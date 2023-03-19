        segment .data
a       db 0x20
b       dw -20
c       dd  100
d       dq -1024


        segment .text
        global _start
_start:
        mov   rax, 0x30
        neg   rax
        neg   byte  [a]
        neg   word  [b]
        neg   dword [c]
        neg   qword [d]
        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
