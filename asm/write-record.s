  .include "record-def.s"
  .include "linux.s"
# PURPOSE:  This function writes a record to the given file descriptor
#
# INPUT:    The file descriptor and a buffer
#
# OUTPUT:   This function produces a status code
#
# STACK LOCAL VARIABLES
#
  .equ ST_WRITE_BUFFER, 8
  .equ ST_FILEDES, 12
  .section .text
  .globl write_record
  .type write_record, @function
write_record:
  pushl %ebp                      # saving base pointer from previous stack frame
  movl  %esp, %ebp                # setting up base pointer of current stack frame

  pushl %ebx                      # not sure why we bother saving content of %ebx
  movl  ST_FILEDES(%ebp), %ebx    # file descriptor argument into %ebx
  movl ST_WRITE_BUFFER(%ebp), %ecx# write buffer address argument into %ecx
  movl $RECORD_SIZE, %edx         # RECORD_SIZE defined in record-def.s
  movl $SYS_WRITE, %eax           # SYS_WRITE defined in linux.s
  int  $LINUX_SYSCALL             # return value in %eax which is passed on

  popl %ebx                       # somehow we want read_record to preserve %ebx

  movl %ebp, %esp                 # restoring stack pointer of current stack frame
  popl %ebp                       # restoring base pointer from previous frame
  ret

