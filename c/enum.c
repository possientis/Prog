#include <stdio.h>


enum fruit {grape, cherry, lemon, kiwi};

struct cant_use_fruit {};   // in same scope

union cannot_use_fruit {};  // in same scope

int main()
{

  enum fruit f1 = grape;

  printf("grape     = %d\n", grape);      // 0 
  printf("cherry    = %d\n", cherry);     // 1
  printf("lemon     = %d\n", lemon);      // 2
  printf("kiwi      = %d\n", kiwi);       // 3

  enum more_fruit {banana = -17, apple, blueberry, mango};

  printf("banana    = %d\n", banana);     // -17
  printf("apple     = %d\n", apple);      // -16
  printf("blueberry = %d\n", blueberry);  // -15
  printf("mango     = %d\n", mango);      // -14

  enum yet_more_fruit { kumquat, raspberry, peach, plum = peach + 2};

  printf("kumquat   = %d\n", kumquat);    // 0
  printf("raspberry = %d\n", raspberry);  // 1
  printf("peach     = %d\n", peach);      // 2
  printf("plum      = %d\n", plum);       // 4

  // declaring a type and a variable at the same time
  enum vegetable1 {carrot, bean, salad} my_vegetable1;

  // declaring a type and a variable separately 
  enum vegetable2 {tomato, broccoli};
  enum vegetable2 my_vegetable2;

  my_vegetable1 = -42;  // no compiler warning !!
  my_vegetable2 = 80;   // be careful
  //  banana = 15;      // can't do that !
  

  enum fruit f2 = grape;

  switch(f2) {
    case grape:
      // do something
      break;
    case cherry:
      // do something
      break;
    case lemon:
      // do something
      break;
    case kiwi:
      // do something
    break;
    default:
      printf("default case\n");
    break;
  };





  return 0;
}
