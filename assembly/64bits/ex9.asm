                                  ; THIS IGNORES SPECIAL CASE OF 0.0
        segment .data
a       dq  3758.678123

        segment .bss
s       db  0                     ; sign      1 bit
e       dw  0                     ; exponent  11 bits (bias 1023)
f       dq  0                     ; fraction  53 bits (52 + implicit '1.')

        segment .text
        global _start
_start:                           ; read 64 bits float and extracts components
        mov rax,  [a]             ; reading 64 bit float (double) from memory
        mov rbx, rax              ; copy in rbx
        rol rbx, 1                ; rotation left, aligning high order bit
        mov rcx, 1                ; mask
        and rbx, rcx              ; extracting sign bit by masking
        mov [s], bl               ; storing sign bit into memory
        mov rbx, rax              ; new copy
        rol rbx, 12               ; aligning 11 exponent bits into low order pos
        mov rcx, 0x7ff            ; 3 + 8 bits = 11 bits mask 
        and rbx, rcx              ; extracting exponent
        sub rbx, 1023             ; subtracting exponent bias 
        mov [e], bx               ; storing exponent into memory
        mov rbx, rax              ; new copy
        mov rcx, 0xfffffffffffff  ; 4 + 48 = 52 bits mask
        and rbx, rcx              ; extracting fraction
        mov rcx, 0x10000000000000 ; 53th bit
        or  rbx, rcx              ; setting 53th bit
        mov [f], rbx              ; storing fraction into memory

_exit:
        ret
        

