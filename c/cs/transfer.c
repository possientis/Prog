/* When performing a cast operation in C that involves both
 * a size change and a change of 'signedness', the operation
 * should change the 'signedness' first
 */

int transfer1(int* p, int y) {
    *p = y;     /* movl %esi, (%rdi) */

    return 0;
}

int transfer2(int* p, char c) {
    *p = c;     /* movsbl %sil, %esi     # signed extends sil to esi
                   movl   %esi, (%rdi)
                */

    return 0;
}

/* TODO */
