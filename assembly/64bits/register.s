      .section .data
a_64: .quad 0x1234567890123456
b_32: .long 0x12345678
c_16: .word 0x9012
d_8:  .byte 0x34
e_8:  .byte 0x56
text1:.ascii "register.s is running ...\x0a"



      .section .text
      .global _start


_start:
      # 64 bits
      movq (a_64), %rax
      movq (a_64), %rbx
      movq (a_64), %rcx
      movq (a_64), %rdx
      movq (a_64), %rdi
      movq (a_64), %rsi
      movq (a_64), %rbp
      movq (a_64), %rsp
      movq (a_64), %r8
      movq (a_64), %r9
      movq (a_64), %r10
      movq (a_64), %r11
      movq (a_64), %r12
      movq (a_64), %r13
      movq (a_64), %r14
      movq (a_64), %r15

      # 32 bits
      movl (b_32), %eax
      movl (b_32), %ebx
      movl (b_32), %ecx
      movl (b_32), %edx
      movl (b_32), %edi
      movl (b_32), %esi
      movl (b_32), %ebp
      movl (b_32), %esp
      movl (b_32), %r8d
      movl (b_32), %r9d
      movl (b_32), %r10d
      movl (b_32), %r11d
      movl (b_32), %r12d
      movl (b_32), %r13d
      movl (b_32), %r14d
      movl (b_32), %r15d

      # 16 bits
      movw (c_16), %ax
      movw (c_16), %bx
      movw (c_16), %cx
      movw (c_16), %dx
      movw (c_16), %di
      movw (c_16), %si
      movw (c_16), %bp
      movw (c_16), %sp
      movw (c_16), %r8w
      movw (c_16), %r9w
      movw (c_16), %r10w
      movw (c_16), %r11w
      movw (c_16), %r12w
      movw (c_16), %r13w
      movw (c_16), %r14w
      movw (c_16), %r15w

      # 8 bits
      movb (d_8), %al
      movb (d_8), %bl
      movb (d_8), %cl
      movb (d_8), %dl
      movb (d_8), %dil
      movb (d_8), %sil
      movb (d_8), %bpl
      movb (d_8), %spl
      movb (d_8), %r8b
      movb (d_8), %r9b
      movb (d_8), %r10b
      movb (d_8), %r11b
      movb (d_8), %r12b
      movb (d_8), %r13b
      movb (d_8), %r14b
      movb (d_8), %r15b

      # 8 bits extra
      movb (e_8), %ah
      movb (e_8), %bh
      movb (e_8), %ch
      movb (e_8), %dh

      # writing some message
      movq  $1, %rax          # write
      movq  $1, %rdi          # stdout 
      movq  $text1, %rsi      # buffer
      movq  $26, %rdx         # 28 bytes
      syscall

      # exiting
      movq $0x3c, %rax
      movq $0,   %rdi
      syscall
