%{
#include "MGL2.tab.h"

int lineno;
int yylen;
int warning(const char *, void*);

%}

ws  [ \t]+
qstring \"[^\"\n]*[\"\n]
nl  \n


%%

{ws}        ;
{qstring}   { yylen = strlen(yytext); 
              yylval.string = strdup(yytext+1); /* skip open quotes */
              if(yylval.string[yylen-2] != '"')
                warning("Unterminated character string", NULL);
              else
                yylval.string[yylen-2] = '\0'; /* remove close quote */
              printf("string = %s\n", yylval.string);

              return QSTRING;
            }
action      { return ACTION; }
execute     { return EXECUTE; }
command     { return COMMAND; }
ignore      { return IGNORE; }
{nl}        { lineno++; }
.           { return yytext[0]; }


%%

int warning(const char *s, void* data)
{
  fprintf(stderr, "%s\n", s);
  return 0;
}
