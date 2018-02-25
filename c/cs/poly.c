#include <stdio.h>

double poly1(double a[], double x, int degree)
{
    int i;
    double result = a[0];
    double xpwr   = x;

    /* 2*N multiplication + N additions where N = degree */
    for(i = 1; i <= degree; ++i) {
        result += a[i]*xpwr;    /* 1 multiplication + 1 addition */
        xpwr   *= x;            /* 1 multiplication */ 
    }

    return result;
}


double poly2(double a[], double x, int degree)
{
    int i;
    double result = a[degree];

    /* N multiplication + N additions where N = degree */
    for(i = degree - 1; i >= 0; --i) {
        result = a[i] + x*result; /* 1 multiplication + 1 addition */
    }

    return result;
}


int main()
{
    int N = 4;
    double a[5] = {1.0,-2.5,-1.0,3.0,1.0};
    double x = 2.0;

    printf("poly1(x) = %lf\n", poly1(a,x,N));
    printf("poly2(x) = %lf\n", poly2(a,x,N));

    int i;
    for(i = 0; i < 10000000; ++i)
        poly2(a,x,N);

    return 0;
}

