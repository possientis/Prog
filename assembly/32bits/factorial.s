# PURPOSE:  Given a number, this program computes the factorial
#
# This program show how to call a function recursively
  .section .data
  # This program has no global data

  .section .text
  .globl _start
  .globl factorial      # to share function with other programs
_start:
  pushl $5              # pushing single argument
  call factorial    
  addl $4, %esp         # restore stack, i.e. removes argument which was pushed
  movl %eax,%ebx        # moving result in %ebx as exit status
  movl $1, %eax         # exit call
  int $0x80

# This is the actual function
  .type factorial, @function
factorial:
  pushl %ebp            # standard function stuff, save base pointer
  movl  %esp, %ebp      # new base pointer set as current stack pointer 
  movl 8(%ebp), %eax    # passed argument into %eax
  cmp $1, %eax          # testing for base case
  je factorial_end      # go to end if argument is 1
  decl %eax             # otherwise decrement argument 
  pushl %eax            # push if for how call to factorial
  call factorial        # recursive call, after call stack clean up at the end
  movl 8(%ebp), %ebx    # %eax has return value, so we reload our argument in %ebx
  imull %ebx, %eax      # multiply argument with return value, result in %eax
factorial_end:
  movl %ebp, %esp       # standard function stuff, restoring stack point
  popl %ebp             # restoring previous base pointer
  ret                   # will pop return address, so stack pointing to pushed arg
