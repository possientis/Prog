#include <stdio.h>
#include <string.h> /* size_t strlen(const char* s); */


/* Warning: This is buggy code */
/* strlen returns a size_t which is an unsigned type */
/* 0U - 1U is 0xFFFFFFFF which is indeed > 0         */

int strlonger (const char *s, const char *t) {
    return strlen(s) - strlen(t) > 0;
}

int strlonger2 (const char *s, const char *t) {
    return (int) (strlen(s) - strlen(t)) > 0;
}


int main() {

    const char* s0 = "";
    const char* s1 = "a";
    const char* s2 = "ab";
    const char* s3 = "abc";

    printf("0U - 1U = 0x%X\n", 0U - 1U);
    printf("\"\" longer than \"\":          %d\n", strlonger(s0,s0));
    printf("\"a\" longer than \"a\":        %d\n", strlonger(s1,s1));
    printf("\"ab\" longer than \"ab\":      %d\n", strlonger(s2,s2));
    printf("\"abc\" longer than \"abc\":    %d\n", strlonger(s3,s3));
    printf("\"\" longer than \"a\":         %d\n", strlonger(s0,s1)); /* 1!!!! */
    printf("\"\" longer than \"a\" (again): %d\n", strlonger2(s0,s1));/* 0 */

    return 0;
}


