        .section .data
format: .asciz  "%s\n"
text:   .asciz  "Hello World!"

        .section .text
        .global main
        .extern printf

main:
        leaq  (format), %rdi  # first parameter
        leaq  (text), %rsi    # second parameter
        xor   %rax, %rax      # 0 floating point parameter    
        call  printf
     
        xor   %rax, %rax
        ret
