// ET_Interpreter.c
#include "ET_Interpreter.h"
#include <list>

template <typename T> class Symbol;

template <typename T>
Expression_Tree<T> ET_Interpreter<T>::interpret(
    ET_Interpreter_Context &context, const std::string &input){

  std::list<Symbol<T>*> parse_tree;

  // more

  if(is_number(input[i])){
    number_insert(input,parse_tree);
  } else if (input[i] == '+'){
    Add *op = new Add(); op->add_precedence(accum_precedence);
    precedence_insert(op,parse_tree);
    // more
  } else if(input[i] == '('){
    handle_parenthesis(context,input,accum_precedence, parse_tree);
  }

  // more
  return Expression_Tree(parse_tree.back()->build());
}
