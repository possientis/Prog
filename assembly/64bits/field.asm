        segment .data
sample  dq  0x1234567812345678
field   dq  0

        segment .text
        global _start

_start:

        ; we want to extract bits 23-51
        mov rax, [sample]   ; move quad word into rax
        shr rax, 23         ; shift to align bit 23 at 0 
        and rax, 0x1fffffff ; select 29 low bits (51 - 23  + 1 = 29)
        mov [field], rax    ; save the field
        shl rax, 23         ; visual check

_next:
        ; we now want to fill in bits 23-51 withbits of field
        mov qword [field], 0x1faabbcc ; 29 bits for field
        mov rax, [sample]
        ror rax, 23             ; rotate to align bit 23 at 0
        shr rax, 29             ; wipe out 29 bits
        shl rax, 29             ; move bits back into alignment
        or  rax, [field]        ; trusting the field in 29 bits
        rol rax, 23             ; realign the bit fields
        mov [sample], rax       ; store the fields in memory

        ret 
