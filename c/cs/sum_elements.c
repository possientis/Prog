#include <stdio.h>


/* Warning: This is buggy code */
float sum_elements(float a[], unsigned length) {
    int i;
    float result = 0;

    /* This is not going to work for length = 0 */
    /* length-1 is 0xFFFFFFFF leading to seg fault */
    /* Also, comparison of unsigned with signed is bad pratice */
    for(i = 0; i <= length-1; ++i)
        result += a[i];

    return result;
}

float sum_elements2(float a[], unsigned length) {

    unsigned int i;
    float result = 0.0;

    for(i = 0; i < length; ++i)
        result += a[i];

    return result;
}


int main() {

    float a[3] = {1.0,2.0,3.0};

    /* seg fault */
/*    printf("sum  = %f\n", sum_elements(a,0)); */
    printf("sum2 = %f\n", sum_elements2(a,0));

    return 0;
}
