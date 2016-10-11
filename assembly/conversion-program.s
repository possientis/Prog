  .include "linux.s"
  .section .data
# This is where it will be stored
tmp_buffer:
  .ascii "\0\0\0\0\0\0\0\0\0\0\0" # 2^32 -1 = 4294967295 (10 digits) + final '\0'
  .section .text
  .globl _start
_start:
  movl %esp, %ebp
#Storage for the result
  pushl $tmp_buffer         # second argument pushed to stack
#Number to convert
  pushl $4294967295         # first argument pushed to stack
  call integer2string
  addl $8, %esp             # restore stack
# Get the character count for our system call
  pushl $tmp_buffer         # first argument of count_chars function
  call count_chars
  addl $4, %esp             # restore stack

# The count goes in %edx for SYS_WRITE
  movl %eax, %edx
# Make the sytem call
  movl $SYS_WRITE, %eax
  movl $STDOUT, %ebx
  movl $tmp_buffer, %ecx
  int   $LINUX_SYSCALL

# Write a carriage return
  pushl $STDOUT
  call write_newline
  addl $4, %esp             # restore stack

# Exit
  movl $SYS_EXIT, %eax
  movl $0, %ebx
  int  $LINUX_SYSCALL
