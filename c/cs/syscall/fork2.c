#include <stdio.h>
#include <stdlib.h>     /* exit     */
#include <unistd.h>     /* fork     */
#include <sys/wait.h>   /* waitpid  */ 

/* we do not know whether parent or child will print first.
 * possible outputs are :
 *
 * acbc
 * abcc
 * bacc
 *
 * But don't forget to flush stdout (or fprintf to stderr)
 * Also, in practice, 'bacc' will dominate. Need to insert some 'sleep(1)' 
 * in key points to see the other two possible outcome.
 */

int main ()
{
    if (fork() == 0) {
        printf("a");
        fflush(stdout);
    }
    else {
        printf("b");
        fflush(stdout);
        waitpid(-1,NULL,0);
    }
    printf("c");
    fflush(stdout);
    exit(0);
}


