        segment .data
name    db      "customer.dat",0
mode    db      "w+",0            ; read and write, truncate or create
fp      dq      0                 ; FILE*

        segment .text
        global main
        extern fopen, fclose

main:
        ; opening file
        lea   rdi, [name]
        lea   rsi, [mode]
        call  fopen
        mov   [fp], rax           ; saving FILE*


        ; closing the file
        mov   rdi, [fp]
        call  fclose

        ; exiting
        mov   rax, 60             ; exit
        mov   rdi, 0              ; exit 0
        syscall
