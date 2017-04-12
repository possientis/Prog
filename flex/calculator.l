%{

#include "y.tab.h"
#include <stdio.h>
extern int yylval;

#define NUMBER 1

%}

%%
[0-9]+      { yylval = atoi(yytext); return NUMBER; }
[ \t]+      ;           /* ignore whitespace */
\n          return 0;   /* logical EOF */
.           return yytext[0];
%%

int yyerror(const char *s)
{
  fprintf(stderr, "%s\n", s);
}
