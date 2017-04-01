#include <stdio.h>
#include <readline/readline.h>
#include <stdlib.h>

void doGuessing(int num) {
  printf("Enter your guess:\n");
  int guess = atoi(readline("$>"));
  if(guess == num) {
    printf("You win!\n");
    return ;
  }

  if(guess < num) {
    printf("Too low!\n");
    doGuessing(num);
  } else {
    printf("Too high!\n");
    doGuessing(num);
  }
}

int main() {
  doGuessing(23);
  return 0;
}

