# PURPOSE:          Count the characters until a null byte is reached
#
# INPUT:            The address of the character string
#
# OUTPUT:           Returns the count in %eax
#
# PROCESS:          
#   registers used:
#                   %ecx - character count
#                   %al  - current character
#                   %edx - current character address

  .type count_chars, @function
  .globl count_chars

  .equ ST_ADDRESS, 8              # position of argument on the stack

count_chars:
  pushl %ebp                      # saving base pointer of previous stack frame
  movl %esp, %ebp                 # setting up base pointer of current stack frame

  movl $0, %ecx                   # initializing character count
  movl ST_ADDRESS(%ebp), %edx     # initializing current character address 

count_loop_begin:
  movb (%edx), %al                # reading current character
  cmpb $0, %al                    # compare current character with zero
  je count_loop_end               # jump if equal (so terminate on null byte)
  incl %ecx                       # increment character count
  incl %edx                       # increment charater address
  jmp count_loop_begin            # go back to the beginning of the loop

count_loop_end:
  movl %ecx, %eax                 # return character in %eax
  movl %ebp, %esp                 # restoring stack (not needed here)
  popl %ebp                       # restoring base pointer of previous stack frame
  ret
