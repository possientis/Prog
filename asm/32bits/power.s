# PURPOSE:     Program to illustrate how functions work
#              This program will compute the value of 
#              2^3 + 5^2

# Everything in the main program is stored in registers,
# so the data section doesn't have anything
  .section .data

  .section .text
  .global _start
_start:
  pushl $3              # push second argument
  pushl $2              # push first argument
  call power            # call the function
  addl $8, %esp         # move the stack pointer back
  pushl %eax            # save the first answer before
                        # making next function call
  pushl $2              # push second argument
  pushl $5              # push first argument
  call power            # new function call
  addl $8, %esp         # restore stack pointer
  
  popl %ebx             # popping first answer
  addl %eax, %ebx       # add first and second answer, result in %ebx

  movl $1, %eax         #exit , %ebx will be returned
  int  $0x80

# PURPOSE:      This function is used to compute
#               the value of a number raised to a power
# INPUT:        First argument - the base number
#               Second argument - the power to raise it to
# OUTPUT:       Will give the result as a return value
#
# NOTES:        The power must be 1 or greater
#
# VARIABLES:    %ebx holds the base number
#               %ecx holds the power
#               
#               -4(%ebp) holds the current result
#               %eax is used for temporary storage

  .type power, @function
power:
  pushl %ebp            # save old base pointer
  movl %esp, %ebp       # make stack pointer the new base pointer
  subl $4, %esp         # get room for our local storage
  movl 8(%ebp), %ebx    # put first argument in %ebx
  movl 12(%ebp), %ecx   # put second argument in %ecx
  movl %ebx, -4(%ebp)   # store current result

power_loop_start:
  cmpl $1, %ecx         # if the power is 1, we are done
  je power_end
  movl -4(%ebp), %eax   # move current result into %eax
  imull %ebx, %eax      # multiply current result by base number
  movl %eax, -4(%ebp)   # store the current result
  decl %ecx             # decrement the power
  jmp power_loop_start  # run for the next power
power_end:
  movl -4(%ebp), %eax   # return value goes into %eax
  movl %ebp, %esp       # restore the stack pointer
  popl %ebp             # restore the base pointer
  ret                  
   
  

  
