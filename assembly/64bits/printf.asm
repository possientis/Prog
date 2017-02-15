        segment .data
format  db "%s",10,0 
text    db "Hello world!",0

        segment .text
        global printf_example
        extern printf

printf_example:
        mov rdi, format
        mov rsi, text
        call printf

        xor eax, eax
        ret

