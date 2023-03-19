%macro print_string 1
          section .data
%%format: db "%s",10,0
          section .text
          extern printf

          lea   rdi, [%%format]
          lea   rsi, [%1]
          xor   rax, rax
          call  printf
%endmacro

          section .text
          global print_string_func
          extern printf

print_string_func:

          section .data
.format   db      "%s",10,0
          section .text
          mov   rsi, rdi    ; string argument of function becomes 2nd arg
          lea   rdi, [.format]
          xor   rax, rax
          call printf
          ret
