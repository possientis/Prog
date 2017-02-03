        segment .text
        global array_fill
        extern random

;       array_fill ( array, size );
array_fill:
.array  equ 0     ; local label for rsp offset of local variable
.size   equ 8     ; local label for rsp offset of local variable
.i      equ 16    ; local label for rsp offset of local variable

        push    rbp
        mov     rbp, rsp
        sub     rsp, 32   ; only need 24 bytes for local vars, but keep 16 align

        mov     [rsp+.array], rdi ; saving first argument in local var
        mov     [rsp+.size],  rsi ; saving second argument in local var
        xor     ecx, ecx          ; setting counter to 0
.more   mov     [rsp+.i], rcx
        call    random    ; may change rdi, rsi, rcx ? see caller vs callee regs
        mov     rcx, [rsp+.i]     ; restoring rcx
        mov     rdi, [rsp+.array] ; restoring rdx
        mov     [rdi+4*rcx], eax  ; random 4 bytes integer into array
        inc     rcx
        cmp     rcx, [rsp+.size]  ; counter < size ?
        jl      .more
        leave
        ret
