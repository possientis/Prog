#include <malloc.h>
#include <stdlib.h>

#include "sbuf.h"


static void P(sem_t *s) { sem_wait(s); }
static void V(sem_t *s) { sem_post(s); }

/* create an empty, bounded, shared FIFO buffer with n slots */
void sbuf_init(sbuf_t *sp, int n)
{
    int *p = (int *) calloc (n, sizeof(int));

    if (p == NULL) {
        fprintf(stderr, "sbuf_init: out of memory error, exiting\n");
        exit(1);
    }

    sp->buf     = p;                /* empty buffer iff front == rear */
    sp->n       = n;                /* buffer holds max of n items */
    sp->front   = 0;                /* buf[(front+1)%n] is first item */ 
    sp->rear    = 0;                /* buf[rear%n] is last item */
    sem_init(&sp->mutex, 0, 1);     /* binary semaphore for locking */
    sem_init(&sp->slots, 0, n);     /* initially, buf has n empty slots */
    sem_init(&sp->items, 0, 0);     /* initially, buf has 0 data items */
}

/* clean up bufer sp */
void sbuf_deinit(sbuf_t *sp)
{
    free(sp->buf);
}


/* insert item onto the rear of shared buffer */
void sbuf_insert(sbuf_t *sp, int item)
{
    P(&sp->slots);                          /* wait for available slots */
    P(&sp->mutex);                          /* lock the buffer */
    sp->buf[(++sp->rear)%(sp->n)] = item;   /* insert the item */
    V(&sp->mutex);                          /* unlock the buffer */
    V(&sp->items);                          /* announce available item */
}

/* remove and return the first item from the buffer sp */
int sbuf_remove(sbuf_t *sp)
{
    int item;
    P(&sp->items);                          /* wait for available item */
    P(&sp->mutex);                          /* lock the buffer */
    item = sp->buf[(++sp->front)%(sp->n)];  /* remove the item */
    V(&sp->mutex);                          /* unlock the buffer */
    V(&sp->slots);                          /* announce available slot */
    return item;
}
