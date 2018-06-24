#include <semaphore.h>

/* global variables */
int readcnt;        /* initially = 0 */
sem_t mutex, w;     /* both initially = 1 */


void P(sem_t *s) { sem_wait(s); }
void V(sem_t *s) { sem_post(s); }

void writer(void)
{
    while (1) {

        P(&w);

        /* critical section, writing happens */

        V(&w);
    }
}

void reader(void)
{
    while (1) {

        P(&mutex);  /* protects readcnt */
        readcnt++;
        if(readcnt == 1) /* first in */
            P(&w);
        V(&mutex);

        /* critical section, reading happens */

        P(&mutex);
        readcnt--;
        if(readcnt == 0) /* last out */
            V(&w);
        V(&mutex);
    }
}
