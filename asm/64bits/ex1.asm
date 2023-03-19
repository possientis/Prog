        segment .data
a8      dq  45
b8      dq  0x20
c8      dq  -20
d8      dq  -30 

a4      dd  45
b4      dd  0x20
c4      dd  -20
d4      dd  -30

a2      dw  45
b2      dw  0x20
c2      dw  -20
d2      dw  -30

a1      db  45
b1      db  0x20
c1      db  -20
d1      db  -30



        segment .text
        global  _start
_start:
        mov     rax, [a8]
        mov     rbx, [b8]
        mov     rcx, [c8]
        mov     rdx, [d8]
        add     rax, rbx
        add     rax, rcx
        add     rax, rdx

_ent4:   
        movsxd  rax, dword [a4]
        movsxd  rbx, dword [b4]
        movsxd  rcx, dword [c4]
        movsxd  rdx, dword [d4]
        add     rax, rbx
        add     rax, rcx
        add     rax, rdx

_ent2:
        movsx   rax, word [a2]
        movsx   rbx, word [b2]
        movsx   rcx, word [c2]
        movsx   rdx, word [d2]
        add     rax, rbx
        add     rax, rcx
        add     rax, rdx

_ent1:
        movsx   rax, byte [a1]
        movsx   rbx, byte [b1]
        movsx   rcx, byte [c1]
        movsx   rdx, byte [d1]
        add     rax, rbx
        add     rax, rcx
        add     rax, rdx
      


_end:
        xor rax, rax
        mov   eax, 1    ; sys call number
        mov   ebx, 0   ; returned status code
        int   0x80
