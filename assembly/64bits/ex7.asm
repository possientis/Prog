        segment .data
a       dq    1024 
b       dq   -4096


        segment .text
        global _start

_start:               ; swapping a and b

        mov rax, [a]
        mov rbx, [b]
        xor rax, rbx  ; a = a ^ b
        xor rbx, rax  ; b = a ^ b
        xor rax, rbx  ; a = a ^ b 
        mov [a], rax
        mov [b], rbx

        ret
