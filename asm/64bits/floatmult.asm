        segment .data
a       dq  -629.67
b       dq   123.7592

        segment .bss
p       dq  0                     ; holding product 
sa      db  0 
ea      dw  0
fa      dq  0
sb      db  0
eb      dw  0
fb      dq  0 
s       db  0 ; sign bit
e       dw  0 ; exponent with bias
f       dq  0 ; 53 bits (53th bit set)
c       dq  0 ; result


        segment .text
        global _start

_start:
        mov rax,  [a]             ; reading 64 bit float (double) from memory
        mov rbx, rax              ; copy in rbx
        rol rbx, 1                ; rotation left, aligning high order bit
        mov rcx, 1                ; mask
        and rbx, rcx              ; extracting sign bit by masking
        mov [sa], bl              ; storing sign bit into memory
        mov rbx, rax              ; new copy
        rol rbx, 12               ; aligning 11 exponent bits into low order pos
        mov rcx, 0x7ff            ; 3 + 8 bits = 11 bits mask 
        and rbx, rcx              ; extracting exponent
        sub rbx, 1023             ; subtracting exponent bias 
        mov [ea], bx              ; storing exponent into memory
        mov rbx, rax              ; new copy
        mov rcx, 0xfffffffffffff  ; 4 + 48 = 52 bits mask
        and rbx, rcx              ; extracting fraction
        mov rcx, 0x10000000000000 ; 53th bit
        or  rbx, rcx              ; setting 53th bit
        mov [fa], rbx             ; storing fraction into memory
_stopa:                           ; a = sa.fa.2^(ea - 52)
        mov rax,  [b]             ; reading 64 bit float (double) from memory
        mov rbx, rax              ; copy in rbx
        rol rbx, 1                ; rotation left, aligning high order bit
        mov rcx, 1                ; mask
        and rbx, rcx              ; extracting sign bit by masking
        mov [sb], bl              ; storing sign bit into memory
        mov rbx, rax              ; new copy
        rol rbx, 12               ; aligning 11 exponent bits into low order pos
        mov rcx, 0x7ff            ; 3 + 8 bits = 11 bits mask 
        and rbx, rcx              ; extracting exponent
        sub rbx, 1023             ; subtracting exponent bias 
        mov [eb], bx              ; storing exponent into memory
        mov rbx, rax              ; new copy
        mov rcx, 0xfffffffffffff  ; 4 + 48 = 52 bits mask
        and rbx, rcx              ; extracting fraction
        mov rcx, 0x10000000000000 ; 53th bit
        or  rbx, rcx              ; setting 53th bit
        mov [fb], rbx             ; storing fraction into memory
_stopb:                           ; b = sb.fb.2^(eb - 52)
        mov rax, [fa]             ; load fraction of a into rax
        imul qword [fb]           ; fa*fb -> rdx:rax
        shr rax, 52               ; keeping highest 12 bits of rax
        shl rdx, 12               ; aligning bits
        or  rax, rdx              ; fa*fb/2^52 -> rax
        mov rcx, 0x20000000000000 ; 54th bit
        mov rbx, rax              ; copy
        and rbx, rcx              ; testing 54th bit
        jz  _cont1
        shr rax, 1                ; 54th bit set becomes 53th bit
_cont1:
        shr rbx, 53               ; result of test as 1 or 0
        mov [f], rax              ; storing fraction
        mov ax, [ea]              ; load exponent for a
        add ax, [eb]              ; ea + eb
        add ax, bx                ; add 1 if 54th bit was set
        mov [e], ax               ; storing exponent
        mov al, [sa]              ; load sign of a
        xor al, [sb]              ; sa*sb -> al
        mov [s], al               ; storing sign

_extract:
        mov rax, [f]                
        mov rcx, 0x10000000000000 ; 53th bit
        xor rax, rcx              ; clearing 53th bit
        mov rbx, 0
        mov bx, [e]               ; exponent with bias
        add bx, 1023              ; restoring bias 
        shl rbx, 52               ; aligning exponent bits
        or rax, rbx               ; including exponent bits
        mov rbx, 0
        mov bl, [s]               ; sign
        shl rbx, 63               ; aligning sign bit
        or rax, rbx               ; including sign bit
        mov [c], rax              ; saving result

_exit:
        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
