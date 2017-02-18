        .section .data
text:   .asciz  "Hello World!\n"

        .section .text
        .global main
        .extern printf

main:
        leaq  (text), %rdi  # parameter 1 for printf
        xor   %eax, %eax    # 0 floating point parameter
        call printf

        xor   %eax, %eax
        ret
        
