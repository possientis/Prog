        .section .data
hello:  .ascii  "Hello World!\n"

        .section .text
        .global  _start

_start:

        # this is 32 bit code, still works under 64 bits
        movl $4, %eax       # sys_write for 32 bits
        movl $1, %ebx       # stdout
        leal (hello), %ecx  # buffer
        movl $13, %edx      # size
        int  $0x80          # syscall for 32 bits

        # this is 64 bit code
        movq $60, %rax      # exit
        movq $0, %rdi       # return value
        syscall
        
