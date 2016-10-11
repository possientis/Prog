#include <string>

class ET_Context;
class ET_Command;

class ET_Command_Factory_Impl{
  public:
    ET_Command_Factory_Impl(ET_Context &context);
    ~ET_Command_Factory_Impl();

    virtual ET_Command make_command(const std::string &s)=0;
    virtual ET_Command make_format_command(const std::string &s)=0;
    virtual ET_Command make_expr_command(const std::string &s)=0;
    virtual ET_Command make_print_command(const std::string &s)=0;
    virtual ET_Command make_eval_command(const std::string &s)=0;
    virtual ET_Command make_quit_command(const std::string &s)=0;
    virtual ET_Command make_macro_command(const std::string &s)=0;

};


