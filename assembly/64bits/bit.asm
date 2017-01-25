        segment .data
a       times 1024 dq 0  ; set with 1024x64 elements  

        segment .text
        global _start

_start:
        mov   rax, 100        ; testing 101th element
        mov   rbx, rax        ; copy bit number to rbx
        shr   rbx, 6          ; qword number of a to test
        mov   rcx, rax        ; copy bit number to rcx
        and   rcx, 0x3f       ; extract rightmost 6 bits       
        xor   rdx, rdx        ; rdx = 0
        bt    [a+8*rbx], rcx  ; test bit
        setc  dl              ; edx equals the tested bit
                              ; guessing test and set, test and reset are atomic
        bts   [a+8*rbx], rcx  ; set the bit, insert into set (test and set)
        btr   [a+8*rbx], rcx  ; clear the bit, remove from set (test and reset) 

        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
