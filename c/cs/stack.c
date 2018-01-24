#include <stdio.h>
#include <string.h>


int len(char *s) {
    return strlen(s);
}

void iptoa(char *s, int *p) 
{
    int val = *p;
    sprintf(s,"%d",val);
}

int intlen(int x) {
    int v;
    char buf[12];
    v = x;
    iptoa(buf,&v);
    return len(buf);
}




int main() {
    int local;
    printf("local at %p\n",&local);
    return 0;
}

