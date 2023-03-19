.include "print_string.s"

        .section .data
text:   .asciz  "Hello World!"

        .section .text
        .global main

main:
        print_string text
 
        xor   %rax, %rax
        ret
