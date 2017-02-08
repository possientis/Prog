      .section .data
a_64: .quad 0x1234567890123456
b_32: .long 0x12345678
c_16: .word 0x9012
d_8:  .byte 0x34
e_8:  .byte 0x56



      .section .text
      .global _start


_start:

      ; 64 bits
      movq [a_64], %rax

      movq $0x3c, %rax
      movq $0,   %rdi
      syscall
