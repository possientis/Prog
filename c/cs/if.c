void cond(int a, int *p) {
    if (p && a > 0)
        *p += a;
}

/*  testq	%rsi, %rsi          # and p p 
	je	.L1                     # if p == 0 then done                     
	testl	%edi, %edi          # and a a
	jle	.L1                     # if <= 0 then done
	addl	%edi, (%rsi)        # *p += a
.L1:                            # 
    rep ret
*/


void goto_cond(int a, int *p) {
    if (p == 0)
        goto done;
    if (a <= 0)
        goto done;
    *p += a;
done:
    return;
}

/* 	testl	%edi, %edi
	jle	.L3
	testq	%rsi, %rsi
	je	.L3
	addl	%edi, (%rsi)
.L4:
.L3:
	rep ret
	
*/
