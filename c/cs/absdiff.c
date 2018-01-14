int absdiff1(int x, int y) {
    if (x < y) 
        return y - x;
    else
        return x - y;
}

/*  movl	%esi, %edx      # edx = y
	subl	%edi, %edx      # edx = y - x
	movl	%edi, %eax      # eax = x
	subl	%esi, %eax      # eax = x - y
	cmpl	%esi, %edi      # compare x to y (care order args for at&t syntax)
	cmovl	%edx, %eax      # if 'less(l)' eax = y - x, signed comparison
	ret
*/

int gotodiff(int x, int y) {
    int result;
    if (x >= y)
        goto x_ge_y;
    result = y - x;
    goto done;
x_ge_y:
    result = x - y;
done:
    return result;
}

/*  same code 	
 *  movl	%esi, %edx
	subl	%edi, %edx
	movl	%edi, %eax
	subl	%esi, %eax
	cmpl	%esi, %edi
	cmovl	%edx, %eax
	ret
*/

unsigned absdiff2(unsigned x, unsigned y) {
    if (x < y) 
        return y - x;
    else
        return x - y;
}

/* 	movl	%esi, %edx      # edx = y  
	subl	%edi, %edx      # edx = y - x
	movl	%edi, %eax      # eax = x
	subl	%esi, %eax      # eax = x - y
	cmpl	%esi, %edi      # compare x to y
	cmovb	%edx, %eax      # if 'below (b)' eax = y - x, unsigned comparison
	ret
*/



