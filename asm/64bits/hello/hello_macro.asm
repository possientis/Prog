%include "print_string.asm"

        section .data
text:   db  "Hello World!",0  ; string null terminated

        section .text
        global main           ; linking with gcc

main:
        print_string text   

        xor   rax, rax        ; returns 0
        ret
