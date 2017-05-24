%{

#include <math.h>
#include "calculator4.tab.h"
#include "table.h"

%}

%%
([0-9]+|([0-9]*\.[0-9]+)([eE][-+]?[0-9]+)?)  { 
              yylval.dval = atof(yytext); 
              return NUMBER; 
            }

[ \t]+      ;           /* ignore whitespace */

[A-Za-z][A-Za-z0-9]*  { /* return symbol pointer */

              yylval.symp = symlook(yytext);
              return NAME; 
            }

\$          { return 0;}


\n | 
.           return yytext[0];

%%


