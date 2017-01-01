      segment .data
a     dd    4
b     dd    4.4
c     times 10 dd 0
d     dw    1, 2
e     db    0xfb
f     db    "hello world", 0

      segment .bss
g     resd    1
h     resd    10
i     resb    100


      segment .text
      global  main    ; let the linker know about main

main:
      push  rbp       ; set up a stack frame for main
      mov   rbp, rsp  ; set rbp to point to the stack frame  
      sub   rsp, 16   ; leave some room for local variable
                      ; leave rsp on a 16 byte boundary
      mov   rax, 0x1a1a1a1a1a1a1a1a
      mov   eax, 100
      mov   rax, 0x1a1a1a1a1a1a1a1a
      mov   rax, 100
      xor   eax, eax  ; set rax to 0 for return value
      leave           ; undo the stack frame manipulation
      ret
