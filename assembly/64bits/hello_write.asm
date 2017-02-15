        section .data
text    db "Hello World!",10  ; string not null terminated
len     equ $-text            ; length of string

        section .text
        global main
        extern write, exit

main:
        mov   edx, len        ; argument 3 is the length
        mov   rsi, text       ; argument 2 is array of char
        mov   edi, 1          ; argument 1 is file descriptor (1 = stdout)
        call write
        xor edi, edi          ; 0 return = success
        call exit
