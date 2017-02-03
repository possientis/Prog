        segment .text
        global array_print
        extern printf

;       array_print ( array, size )
print:
.array  equ 0       ; local label for rsp offset of local variable
.size   equ 8       ; local label for rsp offset of local variable
.i      equ 16      ; local label for rsp offset of local variable

        push  rbp
        mov   rbp, rsp
        sub   rsp, 32   ; only need 24 bytes for local vars, but keep 16 align  

        mov   [rsp+.array], rdi ; saving first argument in local var
        mov   [rsp+.size], rsi  ; saving second argument in local var
        xor   ecx, ecx          ; setting counter to 0
        ; TODO compare with array_fill

