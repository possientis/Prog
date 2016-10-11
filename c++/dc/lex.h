// lex.h: input and lexical analysis declarations
#ifndef LEX_INCLUDED
#define LEX_INCLUDED

enum token_value {
  NAME,     NUMBER,     END,
  PLUS='+', MINUS='-',  MUL='*',  DIV='/',
  PRINT=';',ASSIGN='=', LP='(',   RP=')'
};

extern token_value curr_tok;
extern double number_value;
extern char name_string[256];

token_value get_token();

#endif
