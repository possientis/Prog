        segment .text
        global array_print
        extern printf

;       array_print ( array, size )
array_print:
.array  equ 0       ; local label for rsp offset of local variable
.size   equ 8       ; local label for rsp offset of local variable
.i      equ 16      ; local label for rsp offset of local variable

        push  rbp
        mov   rbp, rsp
        sub   rsp, 32   ; only need 24 bytes for local vars, but keep 16 align  

        mov   [rsp+.array], rdi ; saving first argument in local var
        mov   [rsp+.size], rsi  ; saving second argument in local var
        xor   ecx, ecx          ; setting counter to 0

        segment .data
.format:
        db  "%10d",0x0a,0

        segment .text
.more   mov   [rsp+.i], rcx     ; saving counter register
        lea   rdi, [.format]    ; setting up printf first argument
        mov   rdx, [rsp+.array] ; loading local var in rdx
        mov   esi, [rdx+rcx*4]  ; setting up printf second argument
        call  printf
        mov   rcx, [rsp+.i]     ; restoring rcx
        inc   rcx
        cmp   rcx, [rsp+.size]  ; counter < size ?
        jl    .more
        leave 
        ret
      
