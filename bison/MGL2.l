%{
#include "MGL2.tab.h"

int lineno;

extern int yylen;

%}

ws  [ \t]+
qstring \"[^\"\n]*[\"\n]
nl  \n


%%

{ws}        ;
{qstring}   { yylval.string = strdup(yytext+1); /* skip open quotes */
              if(yylval.string[yylen-2] != '"')
                warning("Unterminated character string", NULL);
              else
                yylval.string[yylen-2] = ' '; /* remove close quote */
              return QSTRING;
            }
action      { return ACTION; }
execute     { return EXECUTE; }
command     { return COMMAND; }
ignore      { return IGNORE; }
{nl}        { lineno++; }
.           { return yytext[0]; }


%%



