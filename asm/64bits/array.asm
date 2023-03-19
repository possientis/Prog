        segment .bss
a       resb    100
b       resw    100
c       resd    100
d       resq    100

        segment .text
        global main

main:
        push  rbp
        mov   rbp, rsp
        sub   rsp, 16

        ; something

        leave
        ret
