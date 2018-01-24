#include <stdio.h>

/* DEPRECATED should not be used, see man page */
/* Sample implementation of library function gets */
char *gets(char *s)
{
    int c;
    char *dest = s;
    int gotchar = 0; /* has at least one char been read? */
    while ((c = getchar()) != '\n' && c != EOF) {
        *dest++ = c;    /* No bounds checking! */
        gotchar = 1;
    }
    *dest++='\0';   /* terminate string */
    if (c == EOF && !gotchar)
        return NULL; /* end of file error */
    return s;
}



int main() {

    char buffer[128];

    gets(buffer);
    printf("%s\n",buffer);

    return 0;
}
