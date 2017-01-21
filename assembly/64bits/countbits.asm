; Counting 1 bits in a memory quad word

; sum = 0;
; i = 0;
; while (i < 64) {
;   sum += data & 1;
;   data = data >> 1;
;   ++i;
; }


        segment .data
data    dq  0xfedcba9876543210  ; 4+3+3+2+3+2+2+1+3+2+2+1+2+1+1+0 = 32
sum     dq  0

        segment .text
        global _start

_start:
        push  rbp
        mov   rbp, rsp
        sub   rsp, 16 

;       Register usage
;       
;       rax: bits being examined
;       rbx: carry bit after bt, setc
;       rcx: loop counter, 0-63
;       rdx: sum of 1 bits

        mov   rax, [data]
        xor   ebx, ebx
        xor   ecx, ecx
        xor   edx, edx      

while:
        cmp   rcx, 64
        jge   end_while
        bt    rax, 0
        setc  bl          ; rbx equals the tested bit
        add   rdx, rbx
        shr   rax, 1
        inc   rcx
        jmp   while

end_while:
        mov   [sum], rdx
        xor   eax, eax
        leave
        ret





        
