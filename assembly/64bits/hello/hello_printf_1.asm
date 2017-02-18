        section .data
format: db  "%s",10,0         ; format string null terminated, using printf
text:   db  "Hello World!",0  ; string null terminated

        section .text
        global main           ; linking with gcc
        extern printf

main:
        lea   rdi, [format]   ; first parameter
        lea   rsi, [text]     ; second parameter
        xor   rax, rax        ; 0 floating point parameter
        call printf


        xor   rax, rax        ; returns 0
        ret
