.text
.globl pushtest
.globl poptest
# attempting to determine the exact semantics of 'pushq %rsp'
# what being pushed onto the stack? (1) the original value of %rsp?
# (2) the decremented value of %rsp ?

# the function returns 0, indicating that (1) is the behaviour on X86_64.
#
pushtest:
    pushq   %rbp
    movq    %rsp, %rbp
    movq    %rsp, %rax
    pushq   %rsp        # semantics unclear
    popq    %rdx
    subq    %rdx, %rax
    movq    %rbp, %rsp
    popq    %rbp
    ret


poptest:
    pushq   %rbp
    movq    %rsp, %rbp
    movq    $0x1234567812345678, %rax
    pushq   %rax
    popq    %rsp    # expecting %rsp = 0x1234567812345678 
    movq    %rsp, %rax
    movq    %rbp, %rsp
    popq    %rbp
    ret
    
