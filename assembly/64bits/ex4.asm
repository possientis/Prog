      segment .data
a     dq  175
b     dq  4097
c     db -23
d     db  23
e     dw -1024
f     dw  1024
g     dd -100000
h     dd  100000
i     dq  245788875


      segment .text
      global _start

_start: 
      mov     rax, [a]
      add     rax, [b]
      movsx   rax, byte   [c] ; move byte, sign extend
      movsx   rax, byte   [d] ; move byte, sign extend
      movzx   rax, byte   [c] ; move byte, zero extend
      movzx   rax, byte   [d] ; move byte, zero extend
      movsx   rax, word   [e] ; move word, sign extend
      movsx   rax, word   [f] ; move word, sign extend
      movzx   rax, word   [e] ; move word, zero extend
      movzx   rax, word   [f] ; move word, zero extend
      movsxd  rax, dword  [g] ; move dword, sign extend
      movsxd  rax, dword  [h] ; move dword, sign extend
      mov     eax, dword  [g] ; move dword, zero extend
      mov     eax, dword  [h] ; move dword, zero extend
_test:
      mov     rax, [i]
      mov     [a], rax        ; move register value into memory
      mov     rbx, rax        ; move value of rax into rbx


      
      xor   rax, rax
      ret


