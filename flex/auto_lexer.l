%{

#define NUMBER 400
#define COMMENT 401
#define TEXT 402
#define COMMAND 403

#pragma GCC dependency "auto_lexer.l" : run '$ flex auto_lexer.l'




%}


%%
[ \t]+          ;

[0-9]+          |
[0-9]+\.[0-9]+  |
\.[0-9]+              { return NUMBER; }

#.*                   { return COMMENT; }

\"[^\"\n]*\"          { return TEXT; }

[a-zA-Z][a-zA-Z0-9]+  { return COMMAND; }

\n                    { return '\n'; }

%%

#include<stdio.h>

int main(int argc, char* argv[])
{
  int val;

  while(val = yylex()) printf("value is %d\n", val);

  return 0;
}



