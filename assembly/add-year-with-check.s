  .include "record-def.s"
  .include "linux.s"

  .section .data
input_file_name:
  .ascii "test.dat\0"

output_file_name:
  .ascii "testout.dat\0"
  
  .section .bss
  .lcomm record_buffer, RECORD_SIZE

  # stack offsets of local variables
  .equ ST_INPUT_DESCRIPTOR, -4
  .equ ST_OUTPUT_DESCRIPTOR, -8

  .section .text
  .globl _start
_start:
  # set up base pointer for current frame and allocate local variables
  movl %esp, %ebp
  subl $8, %esp  

  # open file for reading
  movl $SYS_OPEN, %eax
  movl $input_file_name, %ebx
  movl $0, %ecx                         # read only
  movl $0666, %edx                      # does it matter?
  int  $LINUX_SYSCALL
  movl %eax, ST_INPUT_DESCRIPTOR(%ebp)  # saving file descriptor 
  #### START DEBUG
#  movl %eax, %ebx
#  movl $SYS_EXIT, %eax
#  int  $LINUX_SYSCALL 

  #### END DEBUG

  # This will test whether %eax is negative
  # if it is not negative, it will jump to
  # continue_processing. Otherwise, it will
  # handle the error condition that the negative 
  # number represents
  cmpl $0,%eax
  jge continue_processing

  # send error
  .section .data
no_open_file_code:
  .ascii "0001: \0"
no_open_file_msg:
  .ascii "Can't open input file\0"

  .section .text
  pushl $no_open_file_msg
  pushl $no_open_file_code
  call error_exit

continue_processing:
   
  # open file for writing
  movl $SYS_OPEN, %eax
  movl $output_file_name, %ebx
  movl $0101, %ecx                      # for writing? create if needed?
  movl $0666, %edx                      # permissions if file created?
  int  $LINUX_SYSCALL
  movl %eax, ST_OUTPUT_DESCRIPTOR(%ebp) # saving file descriptor

loop_begin:
  pushl ST_INPUT_DESCRIPTOR(%ebp)       # pushing second argument
  pushl $record_buffer                  # pushing first argument
  call read_record
  addl $8, %esp                         # restoring stack

  # read-record returns the number of bytes read. if it is not the same
  # number as the record size, then either an error has occurred, or the
  # end of file has been reached. Either way, we are quitting

  cmpl $RECORD_SIZE, %eax
  jne  loop_end
 
  # increment the age
  incl record_buffer + RECORD_AGE       # we are not using any '$' sign here

  # write out the record
  pushl ST_OUTPUT_DESCRIPTOR(%ebp)      # pushing second argument
  pushl $record_buffer                  # pushing first argument
  call write_record
  addl $8, %esp                         # restoring stack

  jmp loop_begin                        # deal with next record of input file

loop_end:
  movl $SYS_EXIT, %eax
  movl $0, %ebx                         # ignoring potential error here
  int  $LINUX_SYSCALL


