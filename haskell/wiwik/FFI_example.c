#include <stdio.h>

int example(int a,int b) 
{
    return a + b;
}

void swap(int *a, int *b) 
{
    int t = *a;
    *a = *b;
    *b = t;
}


void qsort(int *xs, int beg, int end)
{
    if (end > beg + 1) {
        int piv = xs[beg];
        int l = beg + 1;
        int r = end;

        while (l < r) {
            if (xs[l] <= piv) {
                l++;
            } else {
                swap(&xs[l],&xs[--r]);
            }
        }

        swap(&xs[--l],&xs[beg]);
        qsort(xs,beg,l);
        qsort(xs,r,end);
    }
}

void invoke(void *fn(int))
{
    int n = 42;
    printf("inside of C, now we'll call Haskell\n");
    fn(n);
    printf("back in side of C again\n");
}
    
