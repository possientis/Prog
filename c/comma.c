#include <stdio.h>

static int temp = 0;

int foo(int x, int y, int z){
  return x + y + z + temp;
}

int main()
{

  int x = 8;
  int y;


  // the comma operator in action
  x++, y = x * x;         // why is ',' useful?
  printf("y = %d\n", y);  // 81

  x++; y = x * x;         // semi-colon too
  printf("y = %d\n", y);  // 100

  x++;
  y = x * x;
  printf("y = %d\n", y);  // 121


  // comma ',' useful here
  for(x = 1, y = 10; x <= 10 && y >= 1; ++x , --y){
    printf("y = %d\n", y);
  }


  // you need (..) around comma operator in function calls
  printf("foo = %d\n", foo(1, (temp=44,2), 3)); // foo = 50
  // ({stmt1;stmt2;stamt3;...;expr;})  -> expr   // need (..) {..} ,final expr, and ;'s
  printf("foo = %d\n", foo(1, ({temp=44;2;}), 3)); // foo = 50

  y = (temp=50,2);
  printf("y = %d\n", y);  // 2

  y = ({temp=51;3;});
  printf("y = %d\n", y);  // 3



  return 0;
}
