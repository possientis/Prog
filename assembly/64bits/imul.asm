        segment .data
a    dq  -1024
lo   dq  0
hi   dq  0


        segment .text
        global _start

_start: ; one operand (128 bits result)
        mov   rax, -4
        imul  qword [a]   ; multiply rax by a ('qword' required)
        mov   [lo], rax   ; store lower part of product
        mov   [hi], rdx   ; store upper part of product

_next:  ; two operands (64 bits result)
        mov   r8, -4
        mov   r9, 15
        mov   r10, -10
        
        mov   rax, -2       
        mov   rdx, 200
        imul  rax, 100      ; multiply rax by 100, result in rax

        mov   rax, 0        ; imul will have no impact
        mov   rdx, 200      ; imul will have no impact 
        imul  r8, qword [a] ; multiply r8 by a, result in r8 ('qword' optional)

        mov   rax, 0        ; imul will have no impact
        mov   rdx, 200      ; imul will have no impact
        imul  r9, r10       ; multiply r9 by r10, result in r9

_final: ; three operands (64 bits result), third op is immediate
        mov   rbx, 0
        mov   rdx, 0 
        imul  rbx, qword [a], 100 ; store a*100 in rbx  ('qword' optional)
        imul  rdx, rbx, 50        ; store 50* rbx in rdx

        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
