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
  .equ O_CREAT_WRONLY_TRUNC 03101
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









