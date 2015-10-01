// ET_Interpreter.h
#ifndef ET_INTERPRETER_INCLUDED
#define ET_INTERPRETER_INCLUDED

#include <string>

template <typename T> class Expression_Tree;
class ET_Interpreter_Context;

template <typename T>
class ET_Interpreter{
  public:
    virtual ~ET_Interpreter();
    Expression_Tree<T>
      interpret(ET_Interpreter_Context &context, const std::string &input);
};

// template, implementation file within header file
#include "ET_Interpreter.c"

#endif

