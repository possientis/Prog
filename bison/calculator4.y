%{
#include <stdio.h>
#include "table.h"

/* grammar where operator precedence and left associativity are explicit */
extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;
extern void yyset_in(FILE*);

%}

%union {
  double dval;
  struct symtab *symp;
}
%token <symp> NAME
%token <dval> NUMBER
%left '+' '-'       /* left associative and at the lowest precedence level */
%left '*' '/'       /* left associative and at the next precedence level */
%nonassoc UMINUS    /* 'UMINUS' pseudo token for unary minus, has no associativity
                        and stands at the highest precedence level */
%type <dval> expression

%%
statement_list: statement '\n'
    |           statement_list statement '\n'
    ;
statement:  NAME '=' expression   { $1->value = $3; }
    |       expression            { printf("= %f\n", $1); } 
    ;
         

expression: expression '+' expression { $$ = $1 + $3; } 
    |       expression '-' expression { $$ = $1 - $3; }
    |       expression '*' expression { $$ = $1 * $3; }
    |       expression '/' expression 
                { if($3 == 0.0)
                    yyerror("divide by zero");
                  else
                    $$ = $1 / $3;
                } /* %prec tells bison to use precedence of UMINUS for rule */
    |       '-' expression %prec UMINUS { $$ = -$2; } 
    |       '(' expression ')'          { $$ = $2; }
    |       NUMBER                      { $$ = $1; } 
    |       NAME                        { $$ = $1->value; }
    ;       

%%


int main()
{

  printf("calculator is running...\n");

  yyset_in(stdin);

  while(!feof(yyin)){
    yyparse();
    printf("returning from parse...\n");
  }

  return 0;
}

int yyerror(const char *s)
{
  fprintf(stderr, "%s\n", s);
}
