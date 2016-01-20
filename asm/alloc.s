# PURPOSE: Program to manage memory usage - allocates
# and deallocates memory as requested
#
# NOTES: The programs using these routines will ask
# for a certain size of memory. We actually
# use more than that size, but we put it
# at the beginning, before the pointer
# we hand back. We add a size field and
# an AVAILABLE/UNAVAILABLE marker. So, the
# memory looks like this
#
# #########################################################
# #Available Marker#Size of memory#Actual memory locations#
# #########################################################
#                                  ^--Returned pointer
# points here
# The pointer we return only points to the actual
# locations requested to make it easier for the
# calling program. It also allows us to change our
# structure without the calling program having to
# change at all.

  .section .data

#######GLOBAL VARIABLES########
# This points to the beginning of the memory we are managing
heap_begin:
  .long 0
# This points to one location past the memory we are managing
current_break:
  .long 0

######STRUCTURE INFORMATION####
# size of space for memory region header
  .equ HEADER_SIZE, 8
# Location of the "available" flag in the header
  .equ HDR_AVAIL_OFFSET, 0
# Location of the size field in the header
  .equ HDR_SIZE_OFFSET, 4

###########CONSTANTS###########
  .equ UNAVAILABLE, 0 #This is the number we will use to mark
# space that has been given out
  .equ AVAILABLE, 1
# This is the number we will use to mark
# space that has been returned, and is available for giving
  .equ SYS_BRK, 45 #system call number for the break
# system call
  .equ LINUX_SYSCALL, 0x80 #make system calls easier to read

  .section .text

##########FUNCTIONS############
##  allocate_init##
# PURPOSE: call this function to initialize the
# functions (specifically, this sets heap_begin and
# current_break). This has no parameters and no
# return value.

  .globl allocate_init
  .type allocate_init,@function
allocate_init:
                                # standard function entry stuff:
  pushl %ebp                    # saving base pointer of previous stack frame
  movl  %esp,%ebp               # setting up base pointer for current frame

# If the brk system call is called with 0 in %ebx, it
# returns the last valid usable address
  movl $SYS_BRK, %eax
# find out where the break is
  movl $0, %ebx
  int  $LINUX_SYSCALL
  incl %eax                     # %eax now has the last valid
                                # address, and we want the
                                # memory location after that
  movl %eax, current_break      # store the current break
  movl %eax, heap_begin         # store the current break as our
                                # first address. This will cause
                                # the allocate function to get
                                # more memory from Linux the
                                #first time it is run
                                # standard function exit stuff
  movl %ebp, %esp               # restoring stack
  popl %ebp                     # restoring base pointer of previous stack frame
  ret                           # exit function 
#####END OF FUNCTION#######
