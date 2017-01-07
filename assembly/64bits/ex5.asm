        segment .data
x1      dq  45
y1      dq  -23
x2      dq  49
y2      dq  -20

        segment .text
        global _start

_start:

        mov   rax, [x1] ; x1
        sub   rax, [x2] ; x1 - x2
        mov   rbx, rax  ; copy
        imul  rax, rbx  ; (x1 - x2)^2
        mov   rcx, rax  ; save

        mov   rax, [y1]
        sub   rax, [y2]
        mov   rbx, rax
        imul  rax, rbx  ; (y1 - y2)^2

        add   rax, rcx  ; (x1 - x2)^2 + (y1 - y2)^2

        ret
