%{

#include <math.h>
#include "calculator5.tab.h"
#include "table.h"

%}

%%
([0-9]+|([0-9]*\.[0-9]+)([eE][-+]?[0-9]+)?)  { 
              yylval.dval = atof(yytext); 
              return NUMBER; 
            }

[ \t]+      ;           /* ignore whitespace */

[A-Za-z][A-Za-z0-9]*  { /* return symbol pointer */

              struct symtab *sp = symlook(yytext);
              
              yylval.symp = sp;

              if(sp->funcptr)
                return FUNC;
              else
                return NAME; 


  
            }

\$          { return 0;}


\n | 
.           return yytext[0];

%%


