        .section .data
format: .asciz  "%s%s %s\n"   # format string null terminated, using printf  
text1:  .asciz  "Hel"         # string1, null terminated
text2:  .asciz  "lo"          # string2, null terminated
text3:  .asciz  "World!"      # string3, null terminated

        .section .text
        .global main          # linking with gcc
        .extern printf

main:
        leaq  (format), %rdi  # first parameter
        leaq  (text1), %rsi   # second parameter
        leaq  (text2), %rdx   # third parameter
        leaq  (text3), %rcx   # fourth parameter
        xor   %rax, %rax      # 0 floating point parameter    
        call  printf
     
        xor   %rax, %rax      # return 0
        ret
