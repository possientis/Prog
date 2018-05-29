#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>


#define MAXLINE 8192

int main() {

    char *buf, *p;
    char arg1[MAXLINE], arg2[MAXLINE], content[MAXLINE];
    int n1=0, n2=0;

    /* extract the two arguments */
    if ((buf = getenv("QUERY_STRING")) != NULL) {
        p = strchr(buf, '&');
        *p = '\0';
        strcpy(arg1,buf);
        strcpy(arg2,p+1);
        n1 = atoi(arg1);
        n2 = atoi(arg2);
    }

    /* make the response body */
    sprintf(content,"Welcome to add.com: ");
    sprintf(content,"%sTHE Internet addition portal.\r\n<p>", content);
    sprintf(content,"%sThe answer is: %d + %d = %d\r\n<p>",
            content, n1, n2, n1 + n2);
    sprintf(content,"%sThanks for visiting!\r\n", content);

    /* generate HTTP response */
    printf("Content-length: %d\r\n", (int) strlen(content));
    printf("Content-type: text/html\r\n\r\n");
    printf("%s", content);
    fflush(stdout);
    exit(0);
}
