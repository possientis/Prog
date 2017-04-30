%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;
extern void yyset_in(FILE*);
extern char buffer[100];
%}

%token NAME NUMBER

%%

statement:
  NAME ':' '<' NUMBER '>'   { printf("NAME = %s\n", buffer); }

%%

int main()
{
  printf("decimal is running...\n");

  yyset_in(stdin);

  while(!feof(yyin)){
    yyparse();
  }

  return 0;
}

int yyerror(const char *s)
{
  fprintf(stderr, "%s\n", s);
}
