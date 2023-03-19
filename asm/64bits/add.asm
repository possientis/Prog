        segment .data
a       dq  151
b       dq  310
sum     dq  0

        segment .text
        global _start

_start:
        push  rbp
        mov   rbp, rsp
        sub   rsp, 16
        mov   rax, 9    ; set rax to 9
        add   [a], rax  ; add rax to a
        mov   rax, [b]  ; get b into rax
        add   rax, 10   ; add 10 to rax
        add   rax, [a]  ; add the content of a
        mov   [sum], rax; save sum in sum 
        mov   rax, 0 

        leave
        mov   eax, 1    ; sys call number
        mov   ebx, 0    ; returned status code
        int   0x80
