#include <ctype.h>
#include<stdio.h>
#include<stdlib.h>

enum {NUM};

char lookahead;

void expr();
void term();
void match(char);
void error();

int main(int argc, char* argv[], char* envp[]){

  lookahead = getchar();
  expr();
  putchar('\n');

  return 0;

}

void expr(){
  term();
  while(1)
    if(lookahead == '+'){
      match('+'); term(); putchar('+');
    }
    else if (lookahead == '-'){
      match('-'); term(); putchar('-');
    }
    else break;
}

void term(){
  if(isdigit(lookahead)){
    putchar(lookahead);
    match(lookahead);
  }
  else{
    error();
  }
}

void match(char c){
  if(lookahead == c){
    lookahead =getchar();
  } else{
    error();
  }
}

void error(){
  printf("syntex error\n");
  exit(1);
}

