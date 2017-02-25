        .section .data
text:   .asciz  "Hello World!"

        .section .text
        .global main
        .extern print_string_func

main:
        leaq  (text), %rdi    # string parameter
        call print_string_func
     
        xor   %rax, %rax
        ret
