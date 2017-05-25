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

%token SCREEN TITLE ITEM COMMAND ACTION EXECUTE MENU QUIT IGNORE
%token ATTRIBUTE VISIBLE INVISIBLE END
%token <string> QSTRING ID

%%

screens:
       | screens screen
       ;
screen : screen_name screen_contents screen_terminator
       | screen_name screen_terminator
       ;

screen_name: SCREEN ID
           | SCREEN
           ;

screen_terminator: END ID
                 | END
                 ;

screen_contents: titles lines

titles:
      | titles title
      ;

title:  TITLE QSTRING
     ;

lines: ITEM

/*
lines: 
     | lines line
     ;

line: ITEM

line: ITEM QSTRING command ACTION action attribute 
    ;

command:
       | COMMAND ID
       ;

action: EXECUTE QSTRING
      | MENU ID
      | QUIT
      | IGNORE
      ;

attribute:
         | ATTRIBUTE VISIBLE
         | ATTRIBUTE INVISIBLE
         ;
*/

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








