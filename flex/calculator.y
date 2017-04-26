%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;
extern void yyset_in(FILE*);

%}

%token NAME NUMBER

%%

statement:  
  NAME '=' expression
| expression            { printf("= %d\n", $1); } 
;
         

expression: 
  NUMBER                { $$ = $1; }
| NUMBER '+' NUMBER     { $$ = $1 + $3; }
| NUMBER '-' NUMBER     { $$ = $1 - $3; }
;       

%%


int main()
{

  printf("main is running...\n");

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
