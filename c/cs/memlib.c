#include <stdio.h>
#include <malloc.h>
#include <errno.h>

#define MAX_HEAP (1L<<32)

/* Private global variables */
static char *mem_heap;      /* points to the first byte of the heap */
static char *mem_brk;       /* points to the last byte of the heap + 1 */
static char *mem_max_addr;  /* max legal heap address + 1 */


/* initializes the memory system model */
void mem_init(void)
{
    mem_heap = (char *) malloc(MAX_HEAP);
    mem_brk  = mem_heap;
    mem_max_addr = mem_heap + MAX_HEAP;
}

/* simple model of the sbrk function. Extends the heap
 * by incr bytes and returns the start address of the new area.
 * In this model, the heap cannot be shrunk
 */

void *mem_sbrk(int incr)
{
    char *old_brk = mem_brk;

    if ( (incr < 0) || (mem_brk + incr) > mem_max_addr) {
        errno = ENOMEM;
        fprintf(stderr,"ERROR: mem_sbrk failed. Ran out of memory...\n");
        return (void *) -1;
    }

    mem_brk += incr;
    return (void*) old_brk;
}

int main()
{
    printf("MAX_HEAP = 0x%lx\n", MAX_HEAP);

    return 0;
}
