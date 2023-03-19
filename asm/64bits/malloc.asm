        segment .bss
pointer dq  0

        segment .text
        global main
        extern malloc
        extern free

main:
        mov rdi, 1000000000
        xor eax, eax
        call malloc
        mov [pointer], rax

        mov rdi, [pointer]
        call free

        ret

        
        
