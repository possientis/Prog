// Command Design Pattern
#include <iostream>
#include <assert.h>

// from https://en.wikipedia.org/wiki/Command_pattern 
// In object-oriented programming, the command pattern is a behavioral 
// design pattern in which an object is used to encapsulate all information 
// needed to perform an action or trigger an event at a later time. This 
// information includes the method name, the object that owns the method 
// and values for the method parameters.
//
// Four terms always associated with the command pattern are command, 
// receiver, invoker and client. A command object knows about receiver 
// and calls a method of the receiver. Values for parameters of the 
// receiver method are stored in the command. The receiver then does 
// the work. An invoker object knows how to execute a command, and 
// optionally does bookkeeping about the command execution. The invoker 
// does not know anything about a concrete command, it knows only about 
// command interface. Both an invoker object and several command objects 
// are held by a client object. The client decides which commands to 
// execute at which points. To execute a command, it passes the command 
// object to the invoker object.
//
// Using command objects makes it easier to construct general components 
// that need to delegate, sequence or execute method calls at a time of 
// their choosing without the need to know the class of the method or the 
// method parameters. Using an invoker object allows bookkeeping about 
// command executions to be conveniently performed, as well as implementing 
// different modes for commands, which are managed by the invoker object, 
// without the need for the client to be aware of the existence of 
// bookkeeping or modes.

// This is the Command interface
class Command {
  public:
    virtual ~Command(){}
  protected:
    Command(){}
  public:
    virtual void execute() = 0;
};

// This is the Invoker class. It is akin to the remote control of an 
// electronic device, or a menu object within an application. It allows
// the client perform actions through a single interface, without
// having to worry about the various part of a system. The invoker class
// it itself very generic and is unaware if the specifics of commands.
class RemoteControl {
  private:
    Command* _powerOn;
    Command* _powerOff;
    Command* _volumeUp;
    Command* _volumeDown;
  public:
    ~RemoteControl();
    RemoteControl(Command* on, Command* off, Command* up, Command* down):
      _powerOn(on), _powerOff(off),_volumeUp(up), _volumeDown(down){}
  public:
    void switchPowerOn()  const;
    void switchPowerOff() const;
    void raiseVolume()    const;
    void lowerVolume()    const;
};

RemoteControl::~RemoteControl(){
  if(_powerOn     != nullptr) delete _powerOn;
  if(_powerOff    != nullptr) delete _powerOff;
  if(_volumeUp    != nullptr) delete _volumeUp; 
  if(_volumeDown  != nullptr) delete _volumeDown;
}

void RemoteControl::switchPowerOn() const {
  assert(_powerOn != nullptr); 
  _powerOn->execute();
}

void RemoteControl::switchPowerOff() const {
  assert(_powerOff != nullptr); 
  _powerOff->execute();
}

void RemoteControl::raiseVolume() const {
  assert(_volumeUp != nullptr); 
  _volumeUp->execute();
}

void RemoteControl::lowerVolume() const {
  assert(_volumeDown != nullptr); 
  _volumeDown->execute();
}

// This is the receiver class. It is the class of objects which will perform
// the various actions. There may be sereral receiver classes comprising
// a system, and the invoker object may invoke commands which applies
// to many different receivers. Typically a menu will execute actions 
// involving not just the application object, but many other sub-objects 
// As this is a simple coding exercise with one receiver object, their
// seems to be a correspondance between the interface of the RemoteControl
// and that of the Televion. However, this correspondance is misleading
// as in general, the interface of the invoker object may have little in
// common with those of the various receiver objects.

class Television {
  private:
    int   _volume;
    bool  _isOn;
  public:
    ~Television(){}
    Television():_volume(10), _isOn(false){}
  public:
    void switchOn();
    void switchOff();
    void volumeUp();
    void volumeDown();
};

void Television::switchOn(){
  if(_isOn == false){
    _isOn = true;
    std::cout << "Television is now switched on\n";
  }
}

void Television::switchOff(){
  if(_isOn){
    _isOn = false;
    std::cout << "Television is now switched off\n";
  }
}

void Television::volumeUp(){
  if(_isOn && _volume < 20){
    _volume++;
    std::cout << "Television volume increased to " << _volume << std::endl;
  }
}

void Television::volumeDown(){
  if(_isOn && _volume > 0){
    _volume--;
    std::cout << "Television volume decreased to " << _volume << std::endl;
  }
}

// These are the concrete command objects. These commands have exact
// knowledge of receiver objects as well as which methods and argument
// should be used when issuing a request to receiver objects.
// As can be seen, the command design pattern relies on a fair amount
// of indirection: client code will call an invoker object (menu, remote)
// which will in turn execute a command, which will send a request to
// to a receiver object, which will finally perform the requested action.
class OnCommand : public Command {
  private:
    Television* _television;
  public:
    ~OnCommand(){} // command does not have ownership of tv, nothing to do
    OnCommand(Television* device):_television(device){}
  public:
    void execute() override;
};
void OnCommand::execute(){
  assert(_television != nullptr);
  _television->switchOn();
}

class OffCommand : public Command {
  private:
    Television* _television;
  public:
    ~OffCommand(){} // command does not have ownership of tv, nothing to do
    OffCommand(Television* device):_television(device){}
  public:
    void execute() override;
};
void OffCommand::execute(){
  assert(_television != nullptr);
  _television->switchOff();
}

class UpCommand : public Command {
  private:
    Television* _television;
  public:
    ~UpCommand(){} // command does not have ownership of tv, nothing to do
    UpCommand(Television* device):_television(device){}
  public:
    void execute() override;
};
void UpCommand::execute(){
  assert(_television != nullptr);
  _television->volumeUp();
}

class DownCommand : public Command {
  private:
    Television* _television;
  public:
    ~DownCommand(){} // command does not have ownership of tv, nothing to do
    DownCommand(Television* device):_television(device){}
  public:
    void execute() override;
};
void DownCommand::execute(){
  assert(_television != nullptr);
  _television->volumeDown();
}

// let's try it all out
int main(){
    // our application will need some reveiver object
    Television device;  // no point using the heap here
    // our application will need an invoker object, which
    // in turns relies on concrete command objects:
    Command* on   = new OnCommand(&device);  // command to switch device on
    Command* off  = new OffCommand(&device); // command to switch device off
    Command* up   = new UpCommand(&device);  // command to turn volume up
    Command* down = new DownCommand(&device);// command to turn volume down
    // now we are ready to create our invoker object which
    // we should think of as some sort of application menu.
    RemoteControl menu(on, off, up, down);  // stack
    // client code is now able to access the invoker object
    menu.switchPowerOn();
    menu.raiseVolume();
    menu.raiseVolume();
    menu.raiseVolume();
    menu.lowerVolume();
    menu.switchPowerOff();
 
  return 0;
}

