  .include "linux.s"
  .equ ST_ERROR_CODE, 8   # first argument
  .equ ST_ERROR_MSG, 12   # second argument (pushed first)
  .globl error_exit
  .type error_exit, @function
error_exit:
  pushl %ebp              # saving base pointer of previous stack frame
  movl  %esp,%ebp         # setting up base pointer of current stack frame

  # write out error code
  movl ST_ERROR_CODE(%ebp), %ecx
  pushl %ecx
  call count_chars
  popl %ecx
  movl %eax, %edx
  movl $STDERR, %ebx
  movl $SYS_WRITE, %eax
  int  $LINUX_SYSCALL

  # write out error message
  movl ST_ERROR_MSG(%ebp), %ecx
  pushl %ecx
  call count_chars
  popl %ecx
  movl %eax, %edx
  movl $STDERR, %ebx
  movl $SYS_WRITE, %eax
  int  $LINUX_SYSCALL

  pushl $STDERR
  call write_newline
  addl $4, %esp           # no real point restoring stack, we re exiting 

  # exit with status 1
  movl $SYS_EXIT, %eax
  movl $1, %ebx
  int  $LINUX_SYSCALL     # not restoring base pointer of previous stack frame
