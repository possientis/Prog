%{
#include "MGL6.tab.h"

int lineno;
int yylen;
int warning(const char *, void*);

%}

ws  [ \t]+
comment #.*
qstring \"[^\"\n]*[\"\n]
id [a-zA-Z][a-zA-Z0-9]*
nl  \n


%%

{ws}        ;
{comment}   ;
{qstring}   { yylen = strlen(yytext); 
              yylval.string = strdup(yytext+1); /* skip open quotes */
              if(yylval.string[yylen-2] != '"')
                warning("Unterminated character string", NULL);
              else
                yylval.string[yylen-2] = '\0'; /* remove close quote */
              return QSTRING;
            }
screen      { return SCREEN; }
title       { return TITLE; }
item        { return ITEM; }
command     { return COMMAND; }
action      { return ACTION; }
execute     { return EXECUTE; }
menu        { return MENU; }
quit        { return QUIT; }
ignore      { return IGNORE; }
attribute   { return ATTRIBUTE; }
visible     { return VISIBLE; }
invisible   { return INVISIBLE; }
end         { return END; }
{id}        { yylval.string = strdup(yytext); return ID; }
{nl}        { lineno++; }
.           { return yytext[0]; }
%%

int warning(const char *s, void* data)
{
  fprintf(stderr, "%s\n", s);
  return 0;
}
