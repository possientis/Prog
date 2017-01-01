      segment .data
a     dq 175
b     dq 4097


      segment .text
      global _start

_start: 
      mov rax, [a]

      xor   rax, rax
      ret


