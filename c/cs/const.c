#include <stdio.h>
#include <string.h>
#include <malloc.h>

const char *gp;

/* initalizing gp so that it points to a part of 
 * memory which does not trigger a segfault when 
 * writing to it
 */

void init()
{
    char* p = (char*) malloc (128);
    strcpy(p,"some runtime chosen message");
    gp = p;
}

void cleanup()
{
    free((void*) gp);
}

void g(const char *argv[])
{
    /* This may seem like a paradox, but this function
     * should not accept an argument of type 'char *argv[]'.
     * What is the big deal? our function guarantees it 
     * will not change the values pointed to by the pointers
     * contained in the argv array. What does it care whether
     * the argument provided allows such a change?
     * The reason is that such a 'char *argv[]' argument
     * would potentially allow 'constness' promises to 
     * be broken. This is how: 
     */

    /*
     * suppose we have some global pointer to const char gp.
     * because our argument argv is declared as const char *argv[]
     * it is permissable to assign argv[0] to gp.
     */

     
     argv[0] = gp; 


}


int main(){

    init();

    char buffer[128];

    char *argv[1];

    argv[0] = buffer;

    strcpy(argv[0],"Initial value");

    printf("initially:\t\t\t%s\n", argv[0]);

    strcpy(argv[0], "New value");

    printf("Later:\t\t\t\t%s\n", argv[0]);

    g(argv);        // argv[0] = gp; by the back door

    printf("After call to function g:\t%s\n", argv[0]);

    printf("checking gp:\t\t\t%s\n", gp);

    strcpy(argv[0],"overwriting gp with no warning");
    strcpy(gp,"This would generate a warning");
  
    printf("checking gp:\t\t\t%s\n", gp);

    cleanup();

    return 0;
}

