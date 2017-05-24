%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;
extern void yyset_in(FILE*);

%}

%token COMMAND

%%
start:  COMMAND
     ;

%%

int main()
{

  printf("MGL is running...\n");

  yyset_in(stdin);

  yyparse();

  printf("parsing was successful...\n");

  return 0;
}

int yyerror(const char *s)
{
  fprintf(stderr, "%s\n", s);
}
