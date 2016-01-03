  .include "linux.s"
  .globl write_newline
  .type write_newline, @function
  .section .data
newline:
  .ascii "\n"
  .section .text
  .equ ST_FILEDES, 8
write_newline:
  pushl %ebp              # saving base pointer of previous stack frame
  movl  %esp, %ebp        # setting up base pointer of current stack frame

  movl $SYS_WRITE, %eax
  movl ST_FILEDES(%ebp), %ebx
  movl $newline, %ecx
  movl $1, %edx           # size of buffer to write (single byte)
  int  $LINUX_SYSCALL

  movl %ebp, %esp         # restoring stack 
  popl %ebp               # restoring base pointer of previous stack frame
  ret
