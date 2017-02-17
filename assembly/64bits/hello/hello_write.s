        .section .data
text:   .ascii "Hello World!\n" # string not null terminated
        .equ len, 13            # need to figure out translation for '$ - text'


        .section .text
        .global main
        .extern write, exit

main:

        movl  $len, %edx        # argument 3 is the length
        movq  $text, %rsi       # argument 2 is array of char
        movl  $1, %edi          # argument 1 is file descriptor (1 = stdout)
        call  write
        xor   %edi, %edi        # 0 return = success 
        call exit
