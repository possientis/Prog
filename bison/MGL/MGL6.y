%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(const char*);
extern FILE *yyin;

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


lines: line 
     | lines line
     ;

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

%%








