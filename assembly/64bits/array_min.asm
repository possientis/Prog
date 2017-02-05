        segment .text
        global  array_min

; page 123
; The min function does not call any other functions, so there is no real need
; for a stack frame and no need to align the stack at a 16 byte boundary. A
; conditional move instruction is used to avoid interrupting the instruction
; pipeline.

; array size needs to beat least two it seems

;       array_min ( array, size )
array_min:
        mov   eax, [rdi]
        mov   rcx, 1

.more   mov   r8d, [rdi+rcx*4]  
        cmp   r8d, eax
        cmovl eax, r8d
        inc   rcx
        cmp   rcx, rsi  ; counter < size ?
        jl    .more
        ret
