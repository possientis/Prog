%{
/*
 * Word recognizer with symbol table
 */

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

\n  { state = lOOKUP; }

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
                case ADV: printf("%s: adverb\n", yytext); break
                case NOUN: printf("%s: noun\n", yytext); break;
                case PREP: printf("%s: preposition\n", yytext); break;
                case PRON: printf("%s: pronoun\n", yytext); break
                case CONJ: printf("%s: conjunction\n", yytext); break;
                default:
                  printf("%s: don't recognize\n", yytext); 
                  break;
              }
            }   
          }
.     /* ignore everything else */ ;

%%






