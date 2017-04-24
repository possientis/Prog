%{
#include <stdio.h>
#define YYSTYPE char const *
int yylex (void);
void yyerror (char const *);
%}

%token TYPENAME ID
%right '='
%left  '+'
%glr-parser

%%
prog:
  %empty
| prog stmt  { printf ("\n"); }
;

stmt:
  expr ';' %dprec 1
| decl      %dprec 2
; 

expr:
  ID                    { printf ("%s ", $$); }
| TYPENAME '(' expr ')'   { printf ("%s <cast> ", $1); }
| expr '+' expr           { printf ("+ "); }
| expr '=' expr           { printf ("= "); }
;

decl:
  TYPENAME declarator ';'           { printf ("%s <declare> ", $1); }
| TYPENAME declarator '=' expr ';'  { printf ("%s <init-declare> ", $1); }
;

declarator:
   ID { printf ("\"%s\" ", $1); }
| '(' declarator ')'
;




