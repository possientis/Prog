/* When performing a cast operation in C that involves both
 * a size change and a change of 'signedness', the operation
 * should change the 'signedness' first
 */

int transfer1(int* p, int y) {
    *p = y;     /* movl %esi, (%rdi) */

    return 0;
}

int transfer2(unsigned* p, int y) {
    *p = y;     /* movl %esi, (%rdi) */

    return 0;
}

int transfer3(int* p, unsigned y) {
    *p = y;     /* movl %esi, (%rdi) */

    return 0;
}

int transfer4(unsigned* p, unsigned y) {
    *p = y;     /* movl %esi, (%rdi) */

    return 0;
}

int transfer5(int* p, char c) {
    *p = c;     /* movsbl %sil, %esi     # sign-extends sil to esi
                   movl   %esi, (%rdi)
                */
    return 0;
}

/* This seems to contradict the 'signedness first' principle */
int transfer6(unsigned* p, char c) {
    *p = c;     /* movsbl %sil, %esi     # sign-extends sil to esi
                   movl   %esi, (%rdi)
                */
    return 0;
}

int transfer7(int* p, unsigned char c) {
    *p = c;     /* movzbl %sil, %esi     # zero-extends sil to esi
                   movl   %esi, (%rdi)
                */
    return 0;
}

int transfer8(unsigned* p, unsigned char c) {
    *p = c;     /* movzbl %sil, %esi     # zero-extends sil to esi
                   movl   %esi, (%rdi)
                */
    return 0;
}

int transfer9(char* p, int y) {
    *p = y;     /* movb %sil, (%rdi) */

    return 0;
}


int tranfer10(char* p, unsigned y) {
    *p = y;     /* movb %sil, (%rdi) */

    return 0;
}

int transfer11(unsigned char* p, int y) {
    *p = y;     /* movb %sil, (%rdi) */

    return 0;
}

int tranfer12(unsigned char* p, unsigned y) {
    *p = y;     /* movb %sil, (%rdi) */

    return 0;
}

int transfer13(long* p, long y) {
    *p = y;     /* movq %rsi, (%rdi) */

    return 0;
}

int transfer14(long* p, int y) {
    *p = y;     /* movslq %esi, rsi 
                   movq   %rsi, (%rdi) */

    return 0;
}

/* seems to contradict 'signedness first' principle */
int transfer15(long* p, unsigned y) {
    *p = y;     /* movl   %esi, %eax   # effectively zero-extends esi to rax ? 
                   movq   %rax, (%rdi) */

    return 0;
}

/* seems to contradict 'signedness first' principle */
int transfer16(unsigned long* p, int y) {
    *p = y;     /* movslq %esi, %rsi    # sign-extends esi to rsi
                   movq   %rsi, (%rdi) */

    return 0;
}

int transfer17(unsigned long* p, unsigned y) {
    *p = y;      /* movl   %esi, %eax   # effectively zero-extends esi to rax ? 
                    movq   %rax, (%rdi) */
    return 0;
}




