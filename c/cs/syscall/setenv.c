#include <stdio.h>
#include <stdlib.h>


int main(int argc, const char *argv[], const char *envp[])
{

    char *p = getenv("A");

    if(p != NULL)
        printf("The environment variable A is set to %s\n", p);
    else
        printf("The environment variable A is not yet set\n");


    printf("Now setting A to the value /usr/share/vim\n");

    if(setenv("A","/usr/share/vim",1) == 0)
        printf("The environment variable A is now set to %s\n", getenv("A"));
    else
        printf("The setting of A was unsuccessful\n");

    printf("\n\nEnvironment variables are as follows:\n");
    int i = 0;
    while (envp[i] != NULL) {
        printf("envp[%d] = %s\n", i, envp[i]);
        ++i;
    }


    return 0;

}
