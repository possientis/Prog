        section .data
format: db  "%s%s %s%s%s%s",10,0  ; format string null terminated, using printf
text1:  db  "Hel",0               ; string1, null terminated 
text2:  db  "lo",0                ; string2, null terminated 
text3:  db  "Wor",0               ; string3, null terminated
text4:  db  "l",0                 ; string4, null terminated
text5:  db  "d",0                 ; string5, null terminated
text6:  db  "!",0                 ; string6, null terminated

        section .text
        global  main            ; linking with gcc
        extern  printf

main:
        lea   rdi,  [format]    ; first parameter 
        lea   rsi,  [text1]     ; second parameter 
        lea   rdx,  [text2]     ; third parameter
        lea   rcx,  [text3]     ; fourth parameter
        lea   r8,   [text4]     ; fifth parameter
        lea   r9,   [text5]     ; sixth parameter
        push  text6             ; seventh argument on the stack

        xor   rax, rax          ; 0 floating point parameter
        call  printf
        pop   rax               ; cleaning up stack

        xor   rax, rax          ; returns 0
        ret
