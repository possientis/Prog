#include <vector>
#include <algorithm>

#ifndef ET_COMMAND_INCLUDED
#include "ET_Command.h"
#endif

class ET_Context;

class ET_Command_Impl{
  public:
  ET_Command_Impl(ET_Context&);
  virtual ~ET_Command_Impl()=0;
  virtual bool exexcute()=0;
  virtual bool unexecute()=0;

};

class Macro_Command: public ET_Command_Impl{
  public:
    // more

    virtual bool execute(){
      for(auto &iter : macro_commands_)
      {
        iter.execute();
      }
      /*
      std::for_each(macro_commands_.begin(),
          macro_commands_.end(),
          [](ET_Command& c){c.execute();}); // lambda expression in C++ !!
      */
          // [](ET_Command c){c.execute();}
          // [](ET_Command* pc){pc->execute();} // not clear why one over the other
          //std::mem_fun_ref(&ET_Command::execute));
      return true;
    };

  private:
    std::vector <ET_Command> macro_commands_;

};
