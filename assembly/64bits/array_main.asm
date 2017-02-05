        segment .text
        global main
        extern atoi
        extern printf
        extern array_create
        extern array_fill
        extern array_print
        extern array_min


main:
.array  equ 0
.size   equ 8

        push  rbp
        mov   rbp, rsp
        sub   rsp, 16

; set default size

        mov   ecx, 10
        mov   [rsp+.size], rcx

; check for argv[1] providing a size

        cmp   edi, 2            ; argc < 2
        jl    .nosize
        mov   rdi, [rsi+8]      ; argument of atoi set to argv[1]  
        call  atoi
        mov   [rsp+.size], rax  

.nosize:

; create the array

        mov   rdi, [rsp+.size] 
        call  array_create
        mov   [rsp+.array], rax

; fill the array with random numbers

        mov   rdi, rax
        mov   rsi, [rsp+.size]
        call  array_fill

; if size <= 20 print the array

        mov   rsi, [rsp+.size]
        cmp   rsi, 20
        jg    .toobig
        mov   rdi, [rsp+.array]
        call  array_print

.toobig:

; print the minimum

        segment .data
.format:
        db    "min: %ld", 0x0a, 0    

        segment .text
        mov   rdi, [rsp+.array]
        mov   rsi, [rsp+.size]
        call  array_min
        lea   rdi, [.format]
        mov   rsi, rax
        call  printf
        
        xor   eax, eax
        leave
        ret








