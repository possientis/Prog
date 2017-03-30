#include <stdio.h>
// ({stmt1;stmt2;stamt3;...;expr;})  -> expr   
// need (..) {..} ,final expr, and ;'s

// An expression which may contain declarations and statements
// very useful as in the following case:

// common macro to define a max
// problem: a (or b) are computed twice ---> computational waste
// if a (or b) has side effect          ---> losing correctness
#define max(a,b) ((a)>(b) ? (a) : (b))


#define maxint(a,b) \
  ({int _a = (a), _b = (b); _a > _b ? _a : _b; })


// if you do not know the type of arguments, you can still do this
// but need to use typeof which is a gnu extension (not standard C)


#define gmax(a,b) \
  ({typeof((a)) _a = (a), _b = (b); _a > _b ? _a : _b; })


int main()
{

  printf("max(3,4) = %d\n", max(3,4));
  printf("maxint(3,4) = %d\n", maxint(3,4));
  printf("gmax(3,4) = %d\n", gmax(3,4));
  printf("gmax(3.14159, 4.14159) = %f\n", gmax(3.14159, 4.14159));

  return 0;
}


