#include <stdio.h>
#include <string.h>

void f(const char *p)   /* f guarantees it will not change data pointed to by p */
{
    /* don't care */
}

void g(const char *argv[]) /* TODO : create an example */
{
    /* don't care */
}


int main(){

    char q[23];             /* data pointed to by q can be changed */
    strcpy(q,"abc");
    f(q);                   /* as expected, there is no issue */

    char *argv[] = {"abc", "def"};
    //g(argv);              /* paradoxically, this cannot be done */ 


    const char c = 'x';
    char *p1;
    const char **p2 = &p1; /* warning !!!! */
    *p2 = &c;
    *p1 = 'X';
    printf("c = %c\n", c); /* because otherwise we are able to change c */

    return 0;
}

