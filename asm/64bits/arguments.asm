        segment .data
format  db      "%s",0x0a,0

        segment .text
        global main
        extern printf

main:
        push  rbp
        mov   rbp, rsp
        sub   rsp, 16 

        mov   rcx, rsi        ; move argv to rcx
        mov   rsi, [rcx]      ; argv[0] in rsi for printf

_loop:
        lea   rdi, [format]   ; first argument for printf
        mov   [rsp], rcx      ; save rcx
        call  printf          ;
        mov   rcx, [rsp]      ; restore rcx
        add   rcx, 8          ; next pointer in argv
        mov   rsi, [rcx]      ; get next argv string
        cmp   rsi, 0
        jnz   _loop

        xor   eax, eax
        leave
        ret
