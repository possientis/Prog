int addl1(int x, int *py) {
    *py += x;               /* addl %edi, (%rsi)            */
    return 0;
}

int subl1(int x, int *py) { 
    *(py + 1) -= x;         /* subl %edi, 4(%rsi)           */
    return 0;
}

int imull1(int x, int *py) {
    py[x] *= 16;            /* movslq %edi, %rdi        # sign-extend edi to rdi
                               sall $4, (%rsi,%rdi,4)   # left-shift 4, 16 = 2^4
                            */
    return 0;
}


int inc1(int *px){
    px[2] += 1;             /* addl $1, 8(%rdi)             */
    return 0;
}
