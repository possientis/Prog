%{
#include "MGL1.tab.h"

int lineno;

%}

ws  [ \t]+
nl  \n


%%

{ws}        ;
command     { return COMMAND; }
{nl}        { lineno++; }
.           { return yytext[0]; }


%%



