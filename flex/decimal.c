#include<stdio.h>
int yylex();
void yyrestart(FILE*);
void yyset_in(FILE*);

extern char* yytext;
extern FILE* yyin;


int main()
{
  yyset_in(stdin);

  FILE* f = yyin;

  while(!feof(f)){
    yylex();
    printf("%s",yytext);
  }
}
