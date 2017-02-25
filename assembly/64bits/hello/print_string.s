# why is the syntax highlighting all messed up??


.macro print_string text
          .section .data
format\@: .asciz "%s\n"
          .section .text
          .extern printf

          lea   (format\@), %rdi
          lea   (text), %rsi
          xor   %rax, %rax
          call  printf
.endm


          .section .text
          .global print_string_func
          .extern printf

print_string_func:

          .section .data
.format:  .asciz   "%s\n"
          .section .text
          movq  %rdi, %rsi  # string argument of function becomes 2nd arg
          leaq  (.format), %rdi
          xor   %rax, %rax
          call printf
          ret
