        section .data
format: db  "%s%s %s",10,0  ; format string null terminated, using printf
text1:  db  "Hel",0         ; string1, null terminated 
text2:  db  "lo",0          ; string2, null terminated 
text3:  db  "World!",0      ; string3, null terminated

        section .text
        global  main        ; linking with gcc
        extern  printf

main:
        lea   rdi, [format] ; first parameter 
        lea   rsi, [text1]  ; second parameter 
        lea   rdx, [text2]  ; third parameter
        lea   rcx, [text3]  ; fourth parameter
        xor   rax, rax      ; 0 floating point parameter
        call  printf

        xor   rax, rax      ; returns 0
        ret
