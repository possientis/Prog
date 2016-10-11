  .include "record-def.s"
  .include "linux.s"

  .section .data
file_name:
  .ascii "test.dat\0"
  
record_buffer_ptr:
  .long 0

  .section .text
  # Main Program
  .globl _start
_start:
  # These are locations on the stack where we will store the input and output
  # file descriptors (we could have used memory addresses in the .data section)
  .equ ST_INPUT_DESCRIPTOR, -4
  .equ ST_OUTPUT_DESCRIPTOR, -8

  movl %esp, %ebp                 # setting up current frame base pointer
  subl $8, %esp                   # allocate space on stack for file descriptors

  call allocate_init              # initialize basic heap allocator
  
  pushl $RECORD_SIZE              # requested size for dynamically allocated buffer
  call  allocate
  movl  %eax, record_buffer_ptr   # saving buffer address

  # open the file
  movl $SYS_OPEN, %eax
  movl $file_name, %ebx
  movl $0, %ecx                   # open in read-only mode
  movl $0666, %edx                # does it matter?
  int  $LINUX_SYSCALL

  # save the file descriptor
  movl %eax, ST_INPUT_DESCRIPTOR(%ebp)

  # eventhough it is constant, we rae saving the output file
  # descriptor in a local variable (stack) so that if we later
  # decide that it isn't going to be STDOUT we can change it
  # easily. STDOUT is defined in linux.s
  movl $STDOUT, ST_OUTPUT_DESCRIPTOR(%ebp) 

record_read_loop:
  pushl ST_INPUT_DESCRIPTOR(%ebp) # second argument pushed to stack
  pushl record_buffer_ptr         # first argument pushed to stack
  call read_record
  addl $8, %esp                   # restoring stack after call

  # read-record returns the number of bytes read. if it is not
  # the number we requested, then it is either the end of file
  # or an error, so we are quitting

  cmpl $RECORD_SIZE, %eax
  jne  finished_reading

  # otherwise, print out the first name, but first we must know it's size
  movl  record_buffer_ptr, %eax
  addl  $RECORD_FIRSTNAME, %eax 
  pushl %eax
  call  count_chars
  addl  $4, %esp                   # restoring stack after call

  # writing first name to output file
  movl %eax, %edx                 # size of first name saved in %edx
  movl ST_OUTPUT_DESCRIPTOR(%ebp), %ebx
  movl $SYS_WRITE, %eax
  movl record_buffer_ptr, %ecx
  addl $RECORD_FIRSTNAME, %ecx
  int  $LINUX_SYSCALL

  pushl ST_OUTPUT_DESCRIPTOR(%ebp)
  call write_newline
  addl $4, %esp                   # restoring stack after call

  jmp record_read_loop

finished_reading:
  pushl record_buffer_ptr
  call deallocate
  movl $SYS_EXIT, %eax  
  movl $0, %ebx
  int  $LINUX_SYSCALL




