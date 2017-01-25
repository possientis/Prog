        segment .data
a       dq  100
b       dq  200
diff    dq  0

        segment .text
        global _start

_start:

        push  rbp
        mov   rbp, rsp
        sub   rsp, 16

        mov   rax, 10
        sub   [a], rax    ; subtract 10 from a
        sub   [b], rax    ; subtract 10 from b
        mov   rax, [b]    ; move b into rax
        sub   rax, [a]    ; set rax to b - a
        mov   [diff], rax ; move difference to diff 
        mov   rax, 0
        leave

        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
