// Command Design Pattern
using System;
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
interface ICommand {          // our demo class is called 'Command'
  void Execute();
}

// This is the Invoker class. It is akin to the remote control of an 
// electronic device, or a menu object within an application. It allows
// the client perform actions through a single interface, without
// having to worry about the various part of a system. The invoker class
// it itself very generic and is unaware if the specifics of commands.
class RemoteControl {
  private readonly ICommand _powerOn;
  private readonly ICommand _powerOff;
  private readonly ICommand _volumeUp;
  private readonly ICommand _volumeDown;

  public RemoteControl(ICommand on, ICommand off, ICommand up, ICommand down){
    this._powerOn     = on;
    this._powerOff    = off;
    this._volumeUp    = up;
    this._volumeDown  = down;
  }

  public void SwitchPowerOn() { _powerOn.Execute();   }
  public void SwitchPowerOff(){ _powerOff.Execute();  }
  public void RaiseVolume()   { _volumeUp.Execute();  }
  public void LowerVolume()   { _volumeDown.Execute();}
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
  private int     _volume = 10;
  private bool    _isOn = false;
  public Television(){}
  public void SwitchOn(){
    if(_isOn == false){
      _isOn = true;
      Console.WriteLine("Televion is now switched on");
    }
  }
  public void SwitchOff(){
    if(_isOn){
      _isOn = false;
      Console.WriteLine("Television is now switched off");
    }
  }
  public void VolumeUp(){
    if(_isOn && _volume < 20){
      _volume++;
      Console.WriteLine("Television volume increased to " + _volume);
    }
  }
  public void VolumeDown(){
    if(_isOn && _volume > 0){
      _volume--;
      Console.WriteLine("Television volume decreased to " + _volume);
    }
  }
}

// These are the concrete command objects. These commands have exact
// knowledge of receiver objects as well as which methods and argument
// should be used when issuing a request to receiver objects.
// As can be seen, the command design pattern relies on a fair amount
// of indirection: client code will call an invoker object (menu, remote)
// which will in turn execute a command, which will send a request to
// to a receiver object, which will finally perform the requested action.
class OnCommand : ICommand {
  private readonly Television _television;
  public OnCommand(Television device){
    _television = device;
  }
  public void Execute(){
    _television.SwitchOn();
  }
}

class OffCommand : ICommand {
  private readonly Television _television;
  public OffCommand(Television device){
    _television = device;
  }
  public void Execute(){
    _television.SwitchOff();
  }
}

class UpCommand : ICommand {
  private readonly Television _television;
  public UpCommand(Television device){
    _television = device;
  }
  public void Execute(){
    _television.VolumeUp();
  }
}

class DownCommand : ICommand {
  private readonly Television _television;
  public DownCommand(Television device){
    _television = device;
  }
  public void Execute(){
    _television.VolumeDown();
  }
}

// let's try it all out
public class Command {
  public static void Main(string[] args){
    // our application will need some reveiver object
    Television device = new Television();
    // our application will need an invoker object, which
    // in turns relies on concrete command objects:
    ICommand on   = new OnCommand(device);  // command to switch device on
    ICommand off  = new OffCommand(device); // command to switch device off
    ICommand up   = new UpCommand(device);  // command to turn volume up
    ICommand down = new DownCommand(device);// command to turn volume down
    // now we are ready to create our invoker object which
    // we should think of as some sort of application menu.
    RemoteControl menu = new RemoteControl(on, off, up, down);
    // client code is now able to access the invoker object
    menu.SwitchPowerOn();
    menu.RaiseVolume();
    menu.RaiseVolume();
    menu.RaiseVolume();
    menu.LowerVolume();
    menu.SwitchPowerOff();
  }
}


