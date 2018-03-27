#include <stdio.h>


int main(int argc, const char *argv[], const char *envp[])
{
    printf("\n\n%d arguments were passed to the program\n", argc);

    int i;
    for(i = 0; i < argc; ++i)
    {
        printf("argv[%d] = %s\n", i, argv[i]);
    }


    printf("\n\nEnvironment variables are as follows:\n");
    i = 0;
    while (envp[i] != NULL) {
        printf("envp[%d] = %s\n", i, envp[i]);
        ++i;
    }



    return 0;

}
