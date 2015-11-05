#include <string>

class ET_Interpreter_Context{
  public:
    ET_Interpreter_Context();
    ~ET_Interpreter_Context();
    int get(std::string variable);
    void set(std::string variable, int value);
    void print();
    void reset();
};
