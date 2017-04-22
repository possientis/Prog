%{

#include <stdio.h>
#include "calculator.tab.h"
extern int yylval;


%}

%%
[0-9]+      { 
              yylval = atoi(yytext); 
              fprintf(stderr, "lexer: number found: %d\n", yylval);
              return NUMBER; 
            }
[ \t]+      ;           /* ignore whitespace */
\n          return 0;   /* logical EOF */
.           return yytext[0];
%%

int yyerror(const char *s)
{
  fprintf(stderr, "%s\n", s);
}
