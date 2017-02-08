        section .data
a_64    dq      0x1234567890123456
b_32    dd      0x12345678
c_16    dw      0x9012 
d_8     db      0x34
e_8     db      0x56

        section .text
        global _start

_start:
        ; 64 bits
        mov   rax, [a_64]
        mov   rbx, [a_64]
        mov   rcx, [a_64]
        mov   rdx, [a_64]
        mov   rdi, [a_64]
        mov   rsi, [a_64]
        mov   rbp, [a_64]
        mov   rsp, [a_64]
        mov   r8,  [a_64]
        mov   r9,  [a_64]
        mov   r10, [a_64]
        mov   r11, [a_64]
        mov   r12, [a_64]
        mov   r13, [a_64]
        mov   r14, [a_64]
        mov   r15, [a_64]

        ; 32 bits
        mov   eax, [b_32]
        mov   ebx, [b_32]
        mov   ecx, [b_32]
        mov   edx, [b_32]
        mov   edi, [b_32]
        mov   esi, [b_32]
        mov   ebp, [b_32]
        mov   esp, [b_32]
        mov   r8d, [b_32] ; 'd' for double
        mov   r9d, [b_32]
        mov   r10d,[b_32]
        mov   r11d,[b_32]
        mov   r12d,[b_32]
        mov   r13d,[b_32]
        mov   r14d,[b_32]
        mov   r15d,[b_32]

        ; 16 bits
        mov   ax,  [c_16]
        mov   bx,  [c_16]
        mov   cx,  [c_16]
        mov   dx,  [c_16]
        mov   di,  [c_16]
        mov   si,  [c_16]
        mov   bp,  [c_16]
        mov   sp,  [c_16]
        mov   r8w, [c_16] ; 'w' for word
        mov   r9w, [c_16]
        mov   r10w,[c_16]
        mov   r11w,[c_16]
        mov   r12w,[c_16]
        mov   r13w,[c_16]
        mov   r14w,[c_16]
        mov   r15w,[c_16]

        ; 8 bits
        mov   al,  [d_8]
        mov   bl,  [d_8]
        mov   cl,  [d_8]
        mov   dl,  [d_8]
        mov   dil, [d_8] ; note special name
        mov   sil, [d_8] ; note special name
        mov   bpl, [d_8] ; note special name
        mov   spl, [d_8] ; note special name
        mov   r8b, [d_8]
        mov   r9b, [d_8]
        mov   r10b,[d_8] ; 'b' for byte
        mov   r11b,[d_8]
        mov   r12b,[d_8]
        mov   r13b,[d_8]
        mov   r14b,[d_8]
        mov   r15b,[d_8]

        ; 8 bits extra
        mov ah, [e_8]
        mov bh, [e_8]
        mov ch, [e_8]
        mov dh, [e_8]



        mov   rax, 0x3c
        mov   rdi, 0
        syscall
