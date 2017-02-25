        section .data
text:   db  "Hello World!",0  ; string null terminated

        section .text
        global main           ; linking with gcc
        extern print_string_func

main:
        lea   rdi, [text]     ; string parameter
        call print_string_func

        xor   rax, rax        ; returns 0
        ret
