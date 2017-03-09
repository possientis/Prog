%{
/*
 * Word recognizer with symbol table
 */

#include<malloc.h>
#include<string.h>

enum {
  LOOKUP = 0, /* default - looking rather than defining */
  VERB,
  ADJ,
  ADV,
  NOUN,
  PREP,
  PRON,
  CONJ
};

int state;
int add_word(int type, const char *word); 
int lookup_word(const char *word);
%}

%%

    /* end of line, return to default state */

\n  { state = LOOKUP; }

    /* whenever a line starts with a reserved part of speech name */
    /* start defining words of that type */
^verb { state = VERB; }
^adj  { state = ADJ; }
^adv  { state = ADV; }
^noun { state = NOUN; }
^prep { state = PREP; }
^pron { state = PRON; }
^conj { state = CONJ; }

    /* a normal word, define it or look it up */
[a-zA-Z]+ {
            if(state != LOOKUP) {
              /* define the current word */
              add_word(state, yytext);
            } else {
              switch(lookup_word(yytext)) {
                case VERB: printf("%s: verb\n", yytext); break;
                case ADJ: printf("%s: adjective\n", yytext); break;
                case ADV: printf("%s: adverb\n", yytext); break;
                case NOUN: printf("%s: noun\n", yytext); break;
                case PREP: printf("%s: preposition\n", yytext); break;
                case PRON: printf("%s: pronoun\n", yytext); break;
                case CONJ: printf("%s: conjunction\n", yytext); break;
                default:
                  printf("%s: don't recognize\n", yytext); 
                  break;
              }
            }   
          }
.     /* ignore everything else */ ;

%%

int main()
{
  yylex();
}

/* define a link list of words and types */
struct word {
  char  *word_name;
  int   word_type;
  struct word *next;
}; 

struct word *word_list; /* first element in word list */

int
add_word(int type, const char *word)
{
  struct word *wp;
  
  if(lookup_word(word) != LOOKUP) {
    printf("!!! warning: word %s already defined \n", word);
    return 0;
  }
  
  /* word not there , allocate new entry and link it on the list */

  wp = (struct word*) malloc(sizeof(struct word));

  wp->next = word_list;
  
  /* have to copy  the word itself as well */
  wp->word_name = (char*) malloc(strlen(word) + 1);
  strcpy(wp->word_name, word);
  wp->word_type = type;
  word_list = wp;
  return 1; /*it worked */
}


int
lookup_word(const char *word)
{
    struct word *wp = word_list;

    /* search down the list looking for word */
    for(; wp; wp = wp->next)
    {
      if(strcmp(wp->word_name, word) == 0)
          return wp->word_type;
    }
    
    return LOOKUP;  /* not found */
}







