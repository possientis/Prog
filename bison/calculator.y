%{
/* grammar where operator precedence and left associativity are implicit */
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;
extern void yyset_in(FILE*);

%}

%token NAME NUMBER

%%

statement:  NAME '=' expression
    |       expression              { printf("= %d\n", $1); } 
    ;
         

expression: expression '+' mulexp   { $$ = $1 + $3; }
    |       expression '-' mulexp   { $$ = $1 - $3; }
    |       mulexp                  { $$ = $1; }
    ;

mulexp:     mulexp '*' primary      { $$ = $1* $3; }
    |       mulexp '/' primary      { if($3 == 0)
                                        yyerror("divide by zero");
                                      else
                                        $$ = $1 / $3;
                                    }
    |       primary                 { $$ = $1; }
    ;

primary:    '(' expression ')'      { $$ =  $2; }
    |       '-' primary             { $$ = -$2; }
    |       NUMBER                  { $$ =  $1; }

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
