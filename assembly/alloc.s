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
##  allocate_init  ##
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

##  allocate  ##
# PURPOSE: This function is used to grab a section of
# memory. It checks to see if there are any
# free blocks, and, if not, it asks Linux
# for a new one.
#
# PARAMETERS: This function has one parameter - the size
# of the memory block we want to allocate
#
# RETURN VALUE:
# This function returns the address of the
# allocated memory in %eax. If there is no
# memory available, it will return 0 in %eax

######PROCESSING########
# Variables used:
#
# %ecx - hold the size of the requested memory
# (first/only parameter)
# %eax - current memory region being examined
# %ebx - current break position
# %edx - size of current memory region
#
# We scan through each memory region starting with
# heap_begin. We look at the size of each one, and if
# it has been allocated. If it’s big enough for the
# requested size, and its available, it grabs that one.
# If it does not find a region large enough, it asks
# Linux for more memory. In that case, it moves
# current_break up

  .globl allocate
  .type allocate,@function
  .equ ST_MEM_SIZE, 8           # stack position of the memory size to allocate
                                # caller pushes this on stack before calling
                                # function. Once function enters, the first thing
                                # we do is push %ebp. So current stack pointer
                                # is 8 bytes higher than position of argument

allocate:
                                # standard function stuff
  pushl %ebp                    # saves base pointer of previous stack frame 
  movl %esp, %ebp               # setting up base pointer of current frame
  movl ST_MEM_SIZE(%ebp), %ecx  # requested size argument saved in %ecx
  movl heap_begin, %eax         # start address of heap in %eax. Note that
                                # code says 'heap_begin' and not '$heap_begin',
                                # i.e. code refers to the address stored in the
                                # word of memory at address $heap_begin, which
                                # was saved by function allocate_init
#search location
  movl current_break, %ebx      # %ebx will hold the current break, which is one
                                # byte after the end of the heap

alloc_loop_begin:               # here we iterate through each memory region
  cmpl %ebx, %eax               # need more memory if these are equal
  je move_break

# grab the size of this memory region
  movl HDR_SIZE_OFFSET(%eax), %edx

# If the space is unavailable, go to the next one
  cmpl $UNAVAILABLE, HDR_AVAIL_OFFSET(%eax)
  je next_location

  cmpl %edx, %ecx               # if region available, compare its size to the 
  jle allocate_here             # requested size. If big enough go to allocat_here

next_location:
  addl $HEADER_SIZE, %eax       # The total size of the memory region is the sum
  addl %edx, %eax               # of the size of the memory region available to
                                # user (currently stored in %edx), plus the size of
                                # header. So adding these two to %eax will make %eax
                                # point to the next memory region (or possibly to
                                # the current break, if heap search is exhausted) 
jmp alloc_loop_begin            # go look at the next memory region

allocate_here:                  # If we've made it here, it means that the region
                                # header of the region to allocate is in %eax. We
                                # need to mark space as unavailable
  movl $UNAVAILABLE, HDR_AVAIL_OFFSET(%eax)
  addl $HEADER_SIZE, %eax       # now points to usable memory
                          
                                # standard function stuff
  movl %ebp, %esp               # restoring stack (in case we moved it in function)
  popl %ebp                     # retoring base pointer of previous stack frame
  ret                           # exit function

move_break:                     # if we've made it here, it means that we have
                                # exhausted all addressable memory, and we need
                                # to ask for more. We need to increase %ebx to 
                                # where we _want_ memory to end. So we add space
                                # for the header structure, and space for the 
                                # memory requested.
  addl $HEADER_SIZE, %ebx
  addl %ecx, %ebx               # requested size currently stored in %ecx
                                # Now is time to ask Linux for more memory

  pushl %eax                    # save registers we care about except %ebp which
  pushl %ecx                    
  pushl %ebx                    
  movl $SYS_BRK, %eax           # reset the break (%ebx has the requested break point)
  int  $LINUX_SYSCALL           # under normal conditions, this should return the new
                                # break in %eax, which will be either 0 if it fails, or
                                # it will be equal to or larger than what we asked for
                                # We don't care in this program where it actuall sets 
                                # the break, so long as %eax is not 0, we do not care
                                # what it is.

  cmpl $0, %eax                 # check for error conditions
  je error
  
  popl %ebx                     # restore saved registers
  popl %ecx                     
  popl %eax
  
  # set this memory as unavailable since we re about to give it away
  movl $UNAVAILABLE, HDR_AVAIL_OFFSET(%eax)
  # set the size of the memory <---- Bug I think because %ecx is size requested
  movl %ecx, HDR_SIZE_OFFSET(%eax) # and it may be that more memory was granted
  addl $HEADER_SIZE, %eax       # move %eax to the actual start of usable memory
                                # %eax now holds the return value
  movl %ebx, current_break      # save the new break
                                # standard function stuff
  movl %ebp, %esp               # restoring stack pointer
  popl %ebp                     # restoring base pointer of previous stack frame 
  ret

error:
  movl $0, %eax                 # on error we return 0 (seems redundant here)
  movl %ebp, %esp               # restoring stack pointer
  popl %ebp                     # restoring base pointer of previous stack frame
#####END OF FUNCTION#######

##deallocate##
#PURPOSE: The purpose of this function is to give back
# a region of memory to the pool after we’re done using it.
#
#PARAMETERS: The only parameter is the address of the memory
# we want to return to the memory pool.
#
#RETURN VALUE: 
# There is no return value
#
#PROCESSING:
# If you remember, we actually hand the program the
# start of the memory that they can use, which is
# 8 storage locations after the actual start of the
# memory region. All we have to do is go back
# 8 locations and mark that memory as available,
# so that the allocate function knows it can use it.
# (This seems very unsafe as a wrong argument can mess up things)
  
  .globl deallocate
  .type deallocate,@function
  # stack position of the memory region to free
  .equ ST_MEMORY_SEG, 4
deallocate:
  # since the function is so simple, we don't do any of the fancy
  # function stuff. i.e. we do not bother to save base pointer
  # of previous stack frame (pushl %ebp). As a consequence, the
  # function argument is now 4 bytes above the stack pointer,
  # we we use as our base pointer (without properly setting
  # a base pointer for the current frame [ movl %esp, %ebp] )
  movl ST_MEMORY_SEG(%esp), %eax  # argument in %eax
  subl $HEADER_SIZE, %eax         # get pointer to real beginning
  # mark memory region as available
  movl $AVAILABLE, HDR_AVAIL_OFFSET(%eax)
  ret                             # exit (no usual function exit stuff)
#####END OF FUNCTION#######






