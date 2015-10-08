#include <string>

class ET_Command;

class Event_Handler{
  public:
    virtual ~Event_Handler()=0;
    virtual void delete_this()=0;
    virtual void handle_input()=0;
};

class ET_Event_Handler: public Event_Handler{
  public:
    virtual void handle_input();
    static ET_Event_Handler *make_handler(bool verbose);
    virtual void prompt_user()=0;
    virtual bool  get_input(std::string &);
    virtual ET_Command make_command(const std::string &input)=0;
    virtual bool execute_command(ET_Command &);
};
