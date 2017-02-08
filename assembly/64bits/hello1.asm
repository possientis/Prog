        section .data 
text    db "Hello World!",0x0a,0  ; string null terminated, using printf

        section .text
        global main               ; linking with gcc
        extern printf            

main:
        push  rbp
        mov   rbp, rsp
        lea   rdi, [text]  ; parameter 1 for printf
        xor   eax, eax    ; 0 floating point parameter (what is that?)
        call  printf

        xor   eax, eax    ; returns 0
        pop   rbp
        ret

