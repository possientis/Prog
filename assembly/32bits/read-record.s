  .include "record-def.s"
  .include "linux.s"
# PURPOSE:  This function reads a record from the file descriptor
#
# INPUT:    The file descriptor and a buffer
#
# OUTPUT:   This function writes the data to the buffer and returns
#           a status code.
#
# STACK LOCAL VARIABLES
#
  .equ ST_READ_BUFFER, 8
  .equ ST_FILEDES, 12
  .section .text
  .globl read_record
  .type read_record, @function
read_record:
  pushl %ebp                      # saving base pointer from previous stack frame
  movl  %esp, %ebp                # setting up base pointer of current stack frame

  pushl %ebx                      # not sure why we bother saving content of %ebx
  movl  ST_FILEDES(%ebp), %ebx    # file descriptor argument into %ebx
  movl  ST_READ_BUFFER(%ebp), %ecx# read buffer address argument into %ecx
  movl $RECORD_SIZE, %edx         # RECORD_SIZE defined in record-def.s
  movl $SYS_READ, %eax            # SYS_READ defined in linux.s
  int  $LINUX_SYSCALL             # return value in %eax which is passed on

  popl %ebx                       # somehow we want read_record to preserve %ebx

  movl %ebp, %esp                 # restoring stack pointer of current stack frame
  popl %ebp                       # restoring base pointer from previous frame
  ret

