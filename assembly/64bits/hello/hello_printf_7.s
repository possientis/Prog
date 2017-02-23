        .section .data
format: .asciz  "%s%s%s %s%s%s%s\n" # format string null terminated, using printf  
text1:  .asciz  "He"                # string1, null terminated
text2:  .asciz  "l"                 # string2, null terminated
text3:  .asciz  "lo"                # string3, null terminated
text4:  .asciz  "Wor"               # string4, null terminated
text5:  .asciz  "l"                 # string5, null terminated
text6:  .asciz  "d"                 # string6, null terminated
text7:  .asciz  "!"                 # string7, null terminated

        .section .text
        .global main            # linking with gcc
        .extern printf

main:
        leaq  (format), %rdi    # first parameter
        leaq  (text1), %rsi     # second parameter
        leaq  (text2), %rdx     # third parameter
        leaq  (text3), %rcx     # fourth parameter
        leaq  (text4), %r8      # fifth parameter
        leaq  (text5), %r9      # sixth parameter
        pushq $text7            # eighth argument on the stack
        pushq $text6            # seventh pushed after eigth

        xor   %rax, %rax        # 0 floating point parameter    
        call  printf
        addq  $16, %rsp         # cleaning up the stack
     
        xor   %rax, %rax        # return 0
        ret
