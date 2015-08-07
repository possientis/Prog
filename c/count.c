/*
 *
 *  Introduction to programming in C
 *
 */
#include <stdio.h>
#define STOP 0
// This comment is not ANSI C compliant
int main()
{
  /* Variable declaration */
  int counter;
  int startPoint;

  /* Prompt the user for input */
  printf("===== Countdown Program =====\n");
  printf("Enter a positive integer: ");
  scanf("%d",&startPoint);

  /* Count down from the input to 0 */
  for (counter = startPoint; counter >= STOP; counter--)
    printf("%d\n", counter);
}

