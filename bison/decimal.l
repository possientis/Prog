%{

#include "decimal.tab.h"
char buffer[100];
char *curpos;

%}

%%
[A-Z]   { 
          strcpy(buffer, yytext);
          curpos = buffer + strlen(yytext);
          strcpy(curpos, " = ");
          curpos += 3;
          return NAME; 
        }

-?((([0-9]+)|([0-9]*\.[0-9]+))([eE][-+]?[0-9]+)?)   { 
          strcpy(curpos, yytext);
          return NUMBER; 
        } 
\n      {
        }
[ \t]+  { 
        }
;.*\n   {
        }
.       {
          return yytext[0];
        }

%%

