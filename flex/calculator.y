%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);

%}

%token NAME NUMBER

%%

statement:  NAME '=' expression
         |  expression            { printf("= %d\n", $1); }
         ;

expression: NUMBER '+' NUMBER     { 
                                    $$ = $1 + $3; 
                                  }
          | NUMBER '-' NUMBER     { 
                                    $$ = $1 - $3; 
                                  }       
          | NUMBER                { 
                                  printf("parser: number found: %d\n", $1);
                                  $$ = $1; 
                                  }
          ;
%%
