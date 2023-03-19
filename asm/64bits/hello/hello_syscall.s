        .section .data
text:   .ascii  "Hello World!\n"

        .section  .text
        .global   _start

_start:

        movq  $1, %rax    # system call 1 write (0 read, 2 open, 3 close)
        movq  $1, %rdi    # first argument for write, file descriptor (stdout) 
        movq  $text, %rsi # second argument for write, buffer
        movq  $13, %rdx   # third argument for write, size 
        syscall           # calling write

        movq  $60, %rax
        movq  $0, %rdi
        syscall
