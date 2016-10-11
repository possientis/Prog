# PURPOSE:   This program finds the  maximum number of a
#           set of data items.

# VARIABLES: The registers have the following uses:
#
# %edi - Holds the index of the data item being examined
# %ebx - Largest data item found
# %eax - Current data item

# The following memory locations are used:
#
# data_items  - contains the item data. A 0 is used
#               to terminate the data

  .section .data

data_items:   # These are the data items
  .long 3,67,34,222,45,75,54,34,44,33,22,11,66,0  # .byte, .int, .long, .ascii

  .section .text
  .global _start
_start:
  movl $0, %edi                   # move 0 into the index register
  movl data_items(,%edi,4), %eax  # load the first byte of data
  movl %eax, %ebx                 # first item is current max

start_loop:
  cmpl $0, %eax                   # check to see if we've hit the end
  je loop_exit                    # je, jg, jge, jl, jle, jmp (think of second arg)
  incl %edi
  movl data_items(,%edi,4), %eax  # load new value
  cmpl %ebx, %eax                 # compare new value with current max
  jle start_loop                  # goes back to start if new value not bigger
  movl %eax, %ebx                 # new value is bigger, becomes new max
  jmp start_loop

loop_exit:
# %ebx is the status code for the exit system call
# and it already has the maximum number
# The largest allowed exit status is 255. So program will output 
# a wierd result if dealing with numbers higher than 255, eventhough
# we are dealing with 32 bits registers.
  movl $1, %eax                   # 1 is the exit() system call
  int $0x80                       # echo $? after running program





