        segment .text
        global _start

_start:
        push rsp
        push rsp
        push rsp

        pop rsp
        pop rsp
        pop rsp
end:
        mov   eax, 1    ; sys call number
        mov   ebx, 0    ; returned status code
        int   0x80
