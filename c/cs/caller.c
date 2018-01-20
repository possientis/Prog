#include <stdio.h>

int swap_add(int *xp, int *yp)
{
    int x = *xp;
    int y = *yp;

    *xp = y;
    *yp = x;

    return x + y;
}


int caller ()
{
    int arg1 = 534;
    int arg2 = 1057;

    int sum  = swap_add(&arg1,&arg2);

    int diff = arg1 - arg2;

    return sum*diff;
    /* (534 + 1057)*(1057 - 534) = 1057^2 - 534^2 = 832093 */
}


int main()
{
    printf("result = %d\n", caller());

    return 0;
}

