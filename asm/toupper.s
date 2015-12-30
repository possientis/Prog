# PURPOSE:    This program converts an input file to an output file
#             with all letters  converted to uppercase.

# PROCESSING: 1. Open the input file
#             2. Open the output file
#             4. While we're not at the end of the input file
#               a. read part of file into our memory buffer
#               b. go through each byte of memory and convert to uppercase
#               c. write the memory buffer to output file
  .section .data
######## CONSTANTS ###########
# system call numbers
  .equ SYS_OPEN , 5
  .equ SYS_WRITE, 4
  .equ SYS_READ, 3
  .equ SYS_CLOSE, 6
  .equ SYS_EXIT, 1
# options for open
  .equ O_RDONLY, 0
  .equ O_CREAT_WRONLY_TRUNC, 03101
# standard file descriptors
  .equ STDIN, 0
  .equ STDOUT, 1
  .equ STDERR, 2
# system call interrupt
  .equ LINUX_SYSCALL, 0x80
  .equ END_OF_FILE, 0 # return value of read which means we've hit the end of file
  .equ NUMBER_ARGUMENTS, 2
  .section .bss
# Buffer    This is where the data is loaded into from the data file and written
#           from into the output file. This should never exceed 16,000 for various
#           reasons.
  .equ BUFFER_SIZE, 500
  .lcomm BUFFER_DATA, BUFFER_SIZE 
  
  .section .text
# STACK POSITIONS
  .equ ST_SIZE_RESERVE, 8
  .equ ST_FD_IN, -4
  .equ ST_FD_OUT, -8
  .equ ST_ARGC, 0   # Number of arguments
  .equ ST_ARGV_0, 4 # Name of program
  .equ ST_ARGV_1, 8 # input file name
  .equ ST_ARGV_2, 12# output file name

  .globl _start
_start:
### INITIALIZE PROGRAM ###
# save the stack pointer
  movl %esp, %ebp
  
# allocate space for our file descriptors on the stack
  subl $ST_SIZE_RESERVE, %esp

open_files:
open_fd_in:
### OPEN INPUT FILE ###
  movl $SYS_OPEN, %eax              # open syscall
  movl ST_ARGV_1(%ebp), %ebx        # input file name into %ebx
  movl $O_RDONLY, %ecx              # read-only fag in %ecx
  movl $0666, %edx                  # permission stuff, not useful for reading
  int  $LINUX_SYSCALL

store_fd_in:
  movl %eax, ST_FD_IN(%ebp)         # save input file descriptor

open_fd_out:
### OPEN OUTPUT FILE ###
  movl $SYS_OPEN, %eax              # open syscall
  movl ST_ARGV_2(%ebp), %ebx        # output file name into %ebx
  movl $O_CREAT_WRONLY_TRUNC, %ecx  # flags for writing to file
  movl $0666, %edx                  # permission, if file created
  int  $LINUX_SYSCALL

store_fd_out:
  movl %eax, ST_FD_OUT(%ebp)        # save output file descriptor

### BEGIN MAIN LOOP ###
read_loop_begin:

### READ A BLOCK FROM THE INPUT FILE ###
  movl $SYS_READ, %eax              # read syscall
  movl ST_FD_IN(%ebp), %ebx         # input file descriptor into %ebx
  movl $BUFFER_DATA, %ecx           # the location to read into
  movl $BUFFER_SIZE, %edx
  int  $LINUX_SYSCALL               # size actually read into %eax


### EXIT IF WE'VE REACHED THE END ###
  cmpl 0, %eax                      # testing for error code (< 0 value)
  jle end_loop                      # if %eax == 0 then end of file

continue_read_loop:
### CONVERT THE BLOCK TO UPPER CASE ###
  pushl $BUFFER_DATA                # location of buffer
  pushl %eax                        # size for buffer
  call convert_to_upper
  popl %eax                         # get the size back
  addl $4, %esp                     # restore stack

### WRITE THE BLOCK OUT TO THE OUTPUT FILE ###
  movl %eax, %edx                   # size of buffer into %edx
  movl $SYS_WRITE, %eax             # write syscall
  movl ST_FD_OUT(%ebp), %ebx        # output file descriptor into %ebx
  movl $BUFFER_DATA, %ecx           # location of buffer into %ecx
  int  $LINUX_SYSCALL

### CONTINUE THE LOOP ###
  jmp read_loop_begin

end_loop:
### CLOSE THE FILES ###
# NOTE: there is no need to do error checking here
#       as error conditions do not mean anything here
  movl $SYS_CLOSE, %eax             # close syscall
  movl ST_FD_OUT(%ebp), %ebx       # output file descriptor into %ebx
  int  $LINUX_SYSCALL

  movl $SYS_CLOSE, %eax
  movl ST_FD_IN(%ebp), %ebx
  int  $LINUX_SYSCALL

### EXIT ###
  movl $SYS_EXIT, %eax
  movl $0, %ebx                     # potentially misleading, did IO error occur?
  int  $LINUX_SYSCALL

# PURPOSE:      This function actually does the conversion to upper case
#
# INPUT:        The first parameter is the location of the block of 
#               memory to convert. The second parameter is the length
#               of that buffer.
#
# OUTPUT:       This function overwrites the current buffer with the 
#               upper-casified version
#
# VARIABLES:    %eax  - beginning of the buffer
#               %ebx  - length of the buffer
#               %edi  - current buffer offset
#               %cl   - current byte being examined (first part of %ecx)
#
### CONSTANTS ###
# The lower boundary of our search
  .equ LOWERCASE_A, 'a'
# The upper boundary of our search
  .equ LOWERCASE_Z, 'z'
# Conversion between upper and lower case
  .equ UPPER_CONVERSION, 'A' - 'a'  

### STACKK STUFF ###
  .equ ST_BUFFER_LEN, 8 # length of buffer
  .equ ST_BUFFER, 12    # actual buffer
convert_to_upper:
  pushl %ebp
  movl  %esp, %ebp

### SET UP VARIABLES ###
  movl ST_BUFFER(%ebp), %eax
  movl ST_BUFFER_LEN(%ebp), %ebx
  movl $0, %edi
  
  cmpl $0, %ebx
  je end_convert_loop         # if zero length buffer, just leave

convert_loop:
  movb (%eax,%edi,1), %cl   # get current byte
  cmpb $LOWERCASE_A, %cl
  jl next_byte
  cmpb $LOWERCASE_Z, %cl
  jg next_byte
  addb $UPPER_CONVERSION, %cl # conversion occurs when 'a' <= %cl <= 'z'
  movb %cl, (%eax,%edi,1)   # store it back

next_byte:
  incl %edi
  cmpl %edi, %ebx
  jne convert_loop

end_convert_loop:
  movl %ebp, %esp             # restore stack, but does not seem necessary here
  popl %ebp                   # restoring old base pointer
  ret                         # pops return address from stack




