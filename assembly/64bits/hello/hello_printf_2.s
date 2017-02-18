        .section .data
format: .asciz  "%s %s\n"     # format string null terminated, using printf  
text1:  .asciz  "Hello"       # string1, null terminated
text2:  .asciz  "World!"      # string2, null terminated

        .section .text
        .global main          # linking with gcc
        .extern printf

main:
        leaq  (format), %rdi  # first parameter
        leaq  (text1), %rsi   # second parameter
        leaq  (text2), %rdx   # third parameter
        xor   %rax, %rax      # 0 floating point parameter    
        call  printf
     
        xor   %rax, %rax
        ret
