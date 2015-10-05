#ifndef ET_COMMAND_INCLUDED
#define ET_COMMAND_INCLUDED

class ET_Command_Impl;

class ET_Command{
  public:
    ET_Command(ET_Command_Impl* = 0);
    ET_Command(const ET_Command&);
    ET_Command &operator=(const ET_Command&);
    ~ET_Command();
    bool execute();
    bool unexecute();

};

#endif
