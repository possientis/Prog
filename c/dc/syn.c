// syn.c: definitions for syntax analysis and evaluation
#include "syn.h"
#include "error.h"
#include "lex.h"
#include "table.h"

double expr()
{
  double left = term();

  for(;;)
    switch(curr_tok){
      case PLUS:
        get_token();
        left += term();
        break;
      case MINUS:
        get_token();
        left -= term();
        break;
      default:
        return left;
    }
}

double term()
{
  double left = prim();

  for(;;)
    switch(curr_tok){
      case MUL:
        get_token();
        left *= term();
        break;
      case DIV:
      {
        get_token();
        double d = prim();
        if(d == 0) return error("divide by zero");
        left /= d;
        break;
      }
      default:
        return left;
    }
}


double prim(){

  switch(curr_tok){
    case NUMBER:
      get_token();
      return number_value;
    case NAME:
      if(get_token() == ASSIGN){
        name* n = insert(name_string);
        get_token();
        n->value = expr();
        return n->value;
      }
      return look(name_string)->value;
    case MINUS:
      get_token();
      return -prim();
    case LP:
    {
      get_token();
      double e = expr();
      if(curr_tok != RP) return error(") expected");
      get_token();
      return e;
    }
    case END:
      return 1; // hmmmm
    default:
      return error("primary expected");
  }
}







