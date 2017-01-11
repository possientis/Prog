        segment .data
a       db  0x73  ; 5 bits are set

        segment .text
        global _start

_start:

        mov rbx, [a]
        mov rax, 0    ; count number of set bits

        mov rcx, rbx
        and rcx, 0x01
        add rax, rcx

        mov rcx, rbx
        and rcx, 0x02
        shr rcx, 1
        add rax, rcx

        mov rcx, rbx
        and rcx, 0x04
        shr rcx, 2
        add rax, rcx

        mov rcx, rbx
        and rcx, 0x08
        shr rcx, 3
        add rax, rcx

        mov rcx, rbx
        and rcx, 0x10
        shr rcx, 4
        add rax, rcx

        mov rcx, rbx
        and rcx, 0x20
        shr rcx, 5
        add rax, rcx

        mov rcx, rbx
        and rcx, 0x40
        shr rcx, 6
        add rax, rcx

        mov rcx, rbx
        and rcx, 0x80
        shr rcx, 7
        add rax, rcx 

_exit:  

        ret
