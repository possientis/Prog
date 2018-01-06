int arith1(int x, int y, int z) {
    int t1 = x + y;                 /* leal (%rdi,%rsi), %eax                   */
    int t3 = t1 & 0xFFFF;           /* movzwl %ax, %eax                         */
    int t2 = z*48;                  /* leal (%rdx,%rdx,3), %edi     # x 3       */ 
                                    /* sall $4, %edi                # 48 = 16x3 */
    int t4 = t2*t3;                 /* imul %edi, %eax                          */
    return t4;
}


int arith2(int x, int y, int z) {
    int t1 = y^x;                   /* xorl %edi, %eax            */
    int t2 = t1 >> 3;               /* sarl $3, %eax              */
    int t3 = ~t2;                   /* notl %eax                  */
    int t4 = t3 - z;                /* subl %edx, %eax            */
    return t4;
}
     



