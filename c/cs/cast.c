/* signed -> signed */

long cast1(long x) {
    long y = (long) x;          /* movq %rdi, %rax */
    return y;
}

long cast2(int x) {
    long y = (long) x;          /* movslq %edi, %rax */
    return y;
}

long cast3(short x) {
    long y = (long) x;          /* movswq %di, %rax */
    return y;
}


long cast4(char x) {
    long y = (long) x;          /* movsbq %dil, %rax */
    return y;
}


int cast5(int x) {
    int y = (int) x;            /* movl %edi, %eax */
    return y;
}


int cast6(short x) {
    int y = (int) x;            /* movswl %di, %eax */
    return y;
}


int cast7(char x) {
    int y = (int) x;            /* movsbl %dil, %eax */
    return y;
}

short cast8(short x) {
    short y = (short) x;        /* movl %edi, %eax (not movw %di, %ax) */
    return y;
}


short cast9(char x) {
    short y = (short) x;        /* movsbw %dil, %ax */
    return y;
}


char cast10(char x) {
    char y = (char) x;          /* movl %edi, %eax (not movb %dil, al) */
    return y;
}

/* unsigned -> signed */

long cast11(unsigned long x) {
    long y = (long) x;          /* movq %rdi, %rax */
    return y;
}

/* Going from 32 bits to 64 bits and from unsigned to signed. */

/* What is the exact semantics of the cast? Does conversion from
 * 32 to 64 bits come first and from unsigned to signed second?
 *
 * Or does the 'signness first' principle apply?
 *
 * Assume the signness first pinciple apply: then the 32 bits 
 * argument contained in %edi is converted from unsigned to signed,
 * which is a 'nop' since this doesn't change the binary representation
 * of the argument. From this point on, the 32 bits argument in %edi is
 * viewed as a signed argument. Hence we expect the compiler to generate 
 * a 'movslq %edi, %rax' (signed extension). However, this is not what
 * we are seeing from the compiler which generates a 'movl %edi, %eax'
 * (semantically equivalent to a 'movzlq %edi, %rax' which does not exist) 
 * Hence we see that 'signness first does not apply' and we can say that 
 * the principle of 'size first' does apply instead.
 * 
 * Note that the principle of 'size first' is a better semantics.
 * Suppose the argument as %edi = 0xFFFFFFFFU. The 'size first'
 * semantics means %rax = 0x00000000FFFFFFFFLU after the (zero)
 * extension, which is then viewed as a signed number.
 * with 'signness first' semantics, we d have %rax = 0xFFFFFF FFFFFFL
 * which makes no sense.
 */
 
long cast12(unsigned int x) {
    long y = (long) x;      /* movl %edi, %eax (there is no movzlq %edi, %rax) */
    return y;
}

/* size first semantics */
/* movzwl %di, %eax semantically equivalent to 'movzwq %di, %rax' */
long cast13(unsigned short x) {
    long y = (long) x;              /* movzwl %di, %eax */
    return y;
}

/* size first semantics. same as movzbq %dil, %rax */
long cast14(unsigned char x) {
    long y = (long) x;              /* movzbl %dil, %eax */
    return y;
}

int cast15(unsigned int x) {
    int y = (int) x;                /* movl %edi, %eax */
    return y;
}

int cast16(unsigned short x) {
    int y = (int) x;                /* movzwl %di, %eax */
    return y;
}

int cast17(unsigned char x) {
    int y = (int) x;                /* movzbl %dil, %eax */
    return y;
}

/* movw %di, %ax is a longer instruction */

short cast18(unsigned short x) {
    short y = (short) x;            /* movl %edi, %eax */
    return y;
}

/* movzbw %dil, %ax is a longer instruction */
short cast19(unsigned char x) {
    short y = (short) x;            /* movzbl %dil, %eax */
    return y;
}

/* movb %dil,%al is a longer instruction */
char cast20(unsigned char x) {
    char y = (char) x;              /* movl %edi, %eax */
    return y;
}

/* signed -> unsigned */
unsigned long cast21(long x) {
    unsigned long y = (unsigned long) x;  /* movq %rdi, %rax */
    return y;
}


/* 'size first' semantics: hence sign-extension */
unsigned long cast22(int x) {
    unsigned long y = (unsigned long) x;  /* movslq %edi, %rax */
    return y;
}

unsigned long cast23(short x) {
    unsigned long y = (unsigned long) x;  /* movswq %di, %rax */
    return y;
}


unsigned long cast24(char x) {
    unsigned long y = (unsigned long) x;  /* movsbq %dil, %rax */
    return y;
}


unsigned int cast25(int x) {
    unsigned int y = (unsigned int) x;  /* movl %edi, %eax */
    return y;
}

unsigned int cast26(short x) {
    unsigned int y = (unsigned int) x;  /* movswl %di, %eax */
    return y;
}

unsigned int cast27(char x) {
    unsigned int y = (unsigned int) x;  /* movsbl %dil, %eax */
    return y;
}

/* was expectting movw %di, %ax but instruction longer */
unsigned short cast28(short x) {
    unsigned short y = (unsigned short) x;  /* movl %edi, %eax */
    return y;
}

/* why not use movsbl %dil, %eax ? instruction shorter */
unsigned short cast29(char x) {
    unsigned short y = (unsigned short) x;  /* movsbw %dil, %ax */
    return y;
}


/* movb %dil, %al is longer */ 
unsigned char cast30(char x) {
    unsigned char y = (unsigned char) x;  /* movl %edi, %eax */
    return y;
}

/* unsigned -> unsigned */

unsigned long cast31(unsigned long x) {
    unsigned long y = (unsigned long) x; /* movq %rdi, %rax */
    return y;
}

/* semantically equivalent to 'movzlq %edi, %rax' which does not exists
 * anyway.... */
unsigned long cast32(unsigned int x) {
    unsigned long y = (unsigned long) x; /* movl %edi, %eax */
    return y;
}


/* semantically equivalent to 'movzwq %di, %rax' which does exist
 * but is longer */
unsigned long cast33(unsigned short x) {
    unsigned long y = (unsigned long) x;    /* movzwl %di, %eax */
    return y;
}

/* semantically equivalent to 'movzbq %dil, %rax' which does exist
 * and of same size */
unsigned long cast34(unsigned char x) {
    unsigned long y = (unsigned long) x;    /* movzbl %dil, %eax */
    return y;
}

unsigned int cast35(unsigned int x) {
    unsigned int y = (unsigned int) x;    /* movl %edi, %eax */
    return y;
}

unsigned int cast36(unsigned short x) {
    unsigned int y = (unsigned int) x;    /* movzwl %di, %eax */
    return y;
}


unsigned int cast37(unsigned char x) {
    unsigned int y = (unsigned int) x;    /* movzbl %dil, %eax */
    return y;
}


/* movw %di, %ax is possible but longer */
unsigned short cast38(unsigned short x) {
    unsigned short y = (unsigned short) x;    /* movl %edi, %eax */
    return y;
}


/* movzbw %dil, %ax possible but longer */
unsigned short cast39(unsigned char x) {
    unsigned short y = (unsigned short) x;    /* movzbl %dil, %eax */
    return y;
}

unsigned char cast40(unsigned char x) {
    unsigned char y = (unsigned char) x;    /* movl %edi, %eax */
    return y;
}



