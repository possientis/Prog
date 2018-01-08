int cmp1 (int x, int y) {
    return x < y;           /* cmpl  %esi, %edi
                               setl   %al           # set 'less'
                               movzbl %al, %eax
                            */
}

int cmp2(unsigned x, unsigned y) {
    return x < y;           /* cmpl   %esi, %edi
                               setb   %al           # set 'below' 
                               movzbl %al, %eax 
                            */
}
