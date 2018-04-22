#include "memlib.h"
#include "mm.h"

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* double word size (bytes) */
#define CHUNKSIZE (1<<12)   /* extend heap by this amount (bytes) */


#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* pack a size and allocated bit into a word */
#define PACK(size,alloc) ((size) | (alloc))


/* read and write a wrod at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (val))

/* read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* given block pointer bp, compute address of its header and footer */
#define HDRP(bp)    ((char *) (bp) - WSIZE)
#define FTRP(bp)    ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* given block pointer bp, compute address of next and previous block */
#define NEXT_BLK(bp) ((char *) (bp) + GET_SIZE(((char *) (bp) - WSIZE)))
#define PREV_BLK(bp) ((char *) (bp) - GET_SIZE(((char *) (bp) - DSIZE)))

void *heap_listp;

static void *extend_heap(size_t words);

int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)
        return -1;

    PUT(heap_listp, 0);                             /* alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));     /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));     /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0,1));         /* Epilogue header */

    heap_listp += (2*WSIZE);

    /* extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
} 


static void *coalesce(void *bp);

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* allocate an even number of words to maintain allignment */
    size = (size % 2) ? (words + 1)*WSIZE : words*WSIZE;
    if((void *) (bp = (char*) mem_sbrk(size)) == (void*) -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp),PACK(size,0));         /* free block header */
    PUT(FTRP(bp),PACK(size,0));         /* free block footer */
    PUT(HDRP(NEXT_BLK(bp)),PACK(0,1));  /* new epilogue header */

    /* coalesce if the previous block was free */
    return coalesce(bp);
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{

}

