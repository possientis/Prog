%{

#include "decimal.tab.h"
char buffer[100];

%}

%%
[A-Z]   { 
          printf("lexer: name found: %s\n", yytext);
          buffer[0] = yytext[0]; 
          buffer[1]=0; 
          return NAME; 
        }

-?((([0-9]+)|([0-9]*\.[0-9]+))([eE][-+]?[0-9]+)?)   { 
          printf("lexer: number found: %s\n", yytext);
          return NUMBER; 
        } 
\n      {
          printf("newline found\n");
        }
[ \t]+  { 
          printf("whitespace found\n");
        }
;.*\n   {
          printf("ignoring comment line\n");
        }
.       {
          printf("character found:%c\n");  
          return yytext[0];
        }

%%

