long local_array(int i)
{
    long a[4] = {2L, 3L, 5L, 7L};
    int idx = i & 3;
    return a[idx];
}


/*  128 bytes of 'red zone' does not need to be allocated
	movq	$2, -32(%rsp)   
	movq	$3, -24(%rsp)
	movq	$5, -16(%rsp)
	movq	$7, -8(%rsp)
	andl	$3, %edi
	movq	-32(%rsp,%rdi,8), %rax
	ret
*/
	
