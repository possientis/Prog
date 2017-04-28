%{
#include <stdio.h>

extern int yylex(void);
extern int yyerror(char*);
extern FILE *yyin;
extern void yyset_in(FILE*);

%}

%token NOUN PRONOUN VERB ADVERB ADJECTIVE PREPOSITION CONJUNCTION

%%

sentence:           simple_sentence   { printf("Parsed a simple sentence.\n"); }
                  | compound_sentence { printf("Parsed a compound sentence.\n"); } 
                  ;

simple_sentence:    subject verb object
                  | subject verb object prep_phrase 
                  ;

compound_sentence:  simple_sentence CONJUNCTION simple_sentence
                  | compound_sentence CONJUNCTION simple_sentence
                  ;

subject:            NOUN 
                  | PRONOUN
                  | ADJECTIVE subject
                  ;

verb:               VERB
                  | ADVERB VERB
                  | verb VERB
                  ;

object:             NOUN
                  | PRONOUN
                  | ADJECTIVE object
                  ;

prep_phrase:        PREPOSITION NOUN
                  ;
%%


int main()
{
  printf("word parser is running ...\n");

  yyset_in(stdin);

  while(!feof(yyin)) {
    yyparse();
  }
 
  return 0;
}

int yyerror(char* s)
{
  fprintf(stderr, "%s\n", s);
}

