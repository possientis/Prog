      segment .data
a     dd 1,-1,2,-2,3

      segment .bss
b     dd 0,0,0,0,0

      segment .text
      global main
      extern copy_array

main:
      
      push  rbp
      mov   rbp, rsp

      lea   rdi,  [b]
      lea   rsi,  [a]
      mov   rdx,  5
      call copy_array 

      leave
      ret
      
