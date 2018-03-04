#include <stdio.h>

#define N 1000
#define M 1500


int sumvec(int v[N])
{
    int i, sum = 0;

    for(i = 0; i < N; ++i)
        sum += v[i];

    return sum;
}


int sumarrayrows(int a[M][N])
{
    int i, j, sum = 0;

    /* good spatial locality, stride-1 reference pattern */
    for(i = 0; i < M; ++i)
        for(j = 0; j < N; ++j)
            sum += a[i][j];

    return sum;
}

int sumarraycols(int a[M][N])
{
    int i, j, sum = 0;

    /* bad spacial locality, stride-N reference pattern */
    for(j = 0; j < N; ++j)
        for(i = 0; i < M; ++i)
            sum += a[i][j];

    return sum;
}


void setup(int a[M][N])
{
    int i,j;

    for(i = 0; i < M; ++i)
        for(j = 0; j < N; ++j)
            a[i][j] = i*i + j*j;
}


/* impact of good locality very clear with profiler */
/* gcc -pg locality.c; ./a.out; gprof a.out | less  */
/* remember gprof does not work on debian stretch   */
int main() {

    int a[M][N];
    setup(a);

    int i, sum1 = 0, sum2 = 0;

    for(i = 0; i < 300; ++i) {
        sum1 += sumarrayrows(a);
        sum2 += sumarraycols(a);
    }
    
    printf("sum1 = %d\n", sum1);
    printf("sum2 = %d\n", sum2);

    return 0;
}

