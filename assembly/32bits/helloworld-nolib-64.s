        .section .data
text1:
  .ascii  "Hello, world!"
text1_end:
  .equ  text1_len, text1_end - text1

        .section .text
        .global _start
_start:
        movq $1, %eax           # sys_write
        movq $1, %rdi           # stdout
        movq $text1, %rsi       # buffer
        movq $text1_len, %rdx   # count
        syscall

        movq $0x3c, %rax        # exit
        movq $0, %rdi           # 0 return value
        syscall
