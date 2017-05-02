%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;
extern void yyset_in(FILE*);

%}

%token NAME NUMBER

%%

statement:  NAME '=' expression
    |       expression            { printf("= %d\n", $1); } 
    ;
         

expression: expression '+' expression { $$ = $1 + $3; } 
    |       expression '-' expression { $$ = $1 - $3; }
    |       expression '*' expression { $$ = $1 * $3; }
    |       expression '/' expression 
                { if($3 == 0)
                    yyerror("divide by zero");
                  else
                    $$ = $1 / $3;
                }
    |       '-' expression            { $$ = -$2; }
    |       '(' expression ')'        { $$ = $2; }
    |       NUMBER                    { $$ = $1; }
    ;       

%%


int main()
{

  printf("calculator is running...\n");

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
