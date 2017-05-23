%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;
extern void yyset_in(FILE*);

%}

%union {
  char *string;   /* string buffer */
}

%token COMMAND ACTION IGNORE EXECUTE ITEM
%token <string> QSTRING ID

%%
items:              /* empty (required for recursive rules) */
     | items item   /* left recursion better for bison */
     ;

item:   ITEM command action
        ;

command: /* empty */
       | COMMAND ID
       ;

action: ACTION IGNORE
      | ACTION EXECUTE QSTRING
      ;

%%

int main()
{

  printf("MGL is running...\n");

  yyset_in(stdin);

  yyparse();

  printf("parsing was successful...\n");

  return 0;
}

int yyerror(const char *s)
{
  fprintf(stderr, "%s\n", s);
  return 1;
}








