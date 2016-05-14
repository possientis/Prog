// Command Design Pattern
#include <stdio.h>
#include <assert.h>
#include <malloc.h>

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

/******************************************************************************/
/*                              Memory log                                    */
/******************************************************************************/

// basic safety scheme against memory leaks
long Command_log(const char* message, const void* address){
  static long memory_check = 0L;
  // Set_log(NULL,NULL) returns current memory_check
  if((message == NULL) && (address == NULL)) return memory_check;
  assert(message != NULL);
  assert(address != NULL);
  // message should contain %lx so fprintf expects third 'address' argument
//  fprintf(stderr, message, address);  // uncomment this line when needed
  memory_check ^= (long) address;     // xor-ing address as sanity check
//  fprintf(stderr, "checksum = %ld\n", memory_check);
  return 0L;
}

int Command_hasMemoryLeak(){
  return Command_log(NULL, NULL) != 0L;
}


/******************************************************************************/
/*                                 Command                                    */
/******************************************************************************/

// This is the Command interface
typedef struct Command_ Command;

struct Command_ {
  int   refcount;
  void  (*execute)(Command* self); // virtual
  void  (*delete)(Command* self);  // virtual
};

// virtual
void Command_execute(Command* self){
  assert(self != NULL);
  void (*execute)(Command* self);
  execute = self->execute;
  assert(execute != NULL);
  execute(self);
}

// virtual
void Command_delete(Command* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){  // virtual dealloc
    void (*delete)(Command* self);
    delete = self->delete;
    assert(delete != NULL);
    delete(self);
  } else {
    Command_log("Deleting copy of command %lx\n", self);
  }
}

Command* Command_copy(Command* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount++;
  Command_log("Making copy of Command %lx\n", self);
  return self;
}


/******************************************************************************/
/*                               RemoteControl                                */
/******************************************************************************/

// This is the Invoker class. It is akin to the remote control of an 
// electronic device, or a menu object within an application. It allows
// the client perform actions through a single interface, without
// having to worry about the various part of a system. The invoker class
// it itself very generic and is unaware if the specifics of commands.

typedef struct RemoteControl_ RemoteControl;

struct RemoteControl_ {
  Command* onPower;
  Command* offPower;
  Command* volumeUp;
  Command* volumeDown;
};

void RemoteControl_init(
  RemoteControl* self, Command* on, Command* off, Command* up, Command* down){
  assert(self != NULL);
  assert(on   != NULL);
  assert(off  != NULL);
  assert(up   != NULL);
  assert(down != NULL);
  self->onPower     = on;
  self->offPower    = off;
  self->volumeUp    = up;
  self->volumeDown  = down;
}

void RemoteControl_destroy(RemoteControl* self){
  assert(self != NULL);

  assert(self->onPower != NULL);
  Command_delete(self->onPower);
  self->onPower = NULL;

  assert(self->offPower != NULL);
  Command_delete(self->offPower);
  self->offPower = NULL;

  assert(self->volumeUp != NULL);
  Command_delete(self->volumeUp);
  self->volumeUp = NULL;

  assert(self->volumeDown != NULL);
  Command_delete(self->volumeDown);
  self->volumeDown = NULL;
}

void RemoteControl_switchPowerOn(RemoteControl* self){
  assert(self != NULL);
  Command_execute(self->onPower);
}

void RemoteControl_switchPowerOff(RemoteControl* self){
  assert(self != NULL);
  Command_execute(self->offPower);
}

void RemoteControl_raiseVolume(RemoteControl* self){
  assert(self != NULL);
  Command_execute(self->volumeUp);
}

void RemoteControl_lowerVolume(RemoteControl* self){
  assert(self != NULL);
  Command_execute(self->volumeDown);
}

/******************************************************************************/
/*                              Television                                    */
/******************************************************************************/

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

typedef struct Television_ Television;

struct Television_ {
  int refcount;
  int volume;
  int isOn;
};


Television* Television_copy(Television* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount++;
  Command_log("Making copy of Television %lx\n", self);
  return self;
}

Television* Television_delete(Television* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    Command_log("Deallocating Television %lx\n", self);
    free(self);
  } else {
    Command_log("Deleting copy of Television %lx\n", self);
  }
}

Television* Television_new(){
  Television* ptr = (Television*) malloc(sizeof(Television));
  assert(ptr != NULL);
  Command_log("Allocating new Television %lx\n", ptr);
  ptr->refcount = 1;
  ptr->volume = 10;
  ptr->isOn = 0;
  return ptr;
}

void Television_switchOn(Television* self){
  assert(self != NULL);
  if(!self->isOn){
    self->isOn = 1;
    printf("Television is now switched on\n");
  }
}

void Television_switchOff(Television* self){
  assert(self != NULL);
  if(self->isOn){
    self->isOn = 0;
    printf("Television is now switched off\n");
  }
}

void Television_volumeUp(Television* self){
  assert(self != NULL);
  if(self->isOn){
    self->volume++;
    printf("Television volume increased to %d\n", self->volume);
  }
}

void Television_volumeDown(Television* self){
  assert(self != NULL);
  if(self->isOn){
    self->volume--;
    printf("Television volume decreased to %d\n", self->volume);
  }
}

int Television_test(){
  // basic new/copy/delete test
  printf("\nnew, copy, delete...\n");
  Television* tv1 = Television_new();
  Television* tv2 = Television_copy(tv1);
  Television_delete(tv1);
  Television_delete(tv2);
  assert(!Command_hasMemoryLeak());
  //
  printf("\ncommands...\n");
  tv1 = Television_new();
  Television_switchOn(tv1);
  Television_volumeUp(tv1);
  Television_volumeUp(tv1);
  Television_volumeUp(tv1);
  Television_volumeDown(tv1);
  Television_switchOff(tv1);
  Television_delete(tv1);
  assert(!Command_hasMemoryLeak());
  return 0;
}



// These are the concrete command objects. These commands have exact
// knowledge of receiver objects as well as which methods and argument
// should be used when issuing a request to receiver objects.
// As can be seen, the command design pattern relies on a fair amount
// of indirection: client code will call an invoker object (menu, remote)
// which will in turn execute a command, which will send a request to
// to a receiver object, which will finally perform the requested action.

/******************************************************************************/
/*                                  OnCommand                                 */
/******************************************************************************/


typedef struct OnCommand_ OnCommand;

struct OnCommand_ {
  Command base;
  Television* television;
};

// override 
void _OnCommand_execute(Command* self){
  assert(self != NULL);
  OnCommand* object = (OnCommand*) self;  // downcast
  Television* television = object->television;
  assert(television != NULL);
  Television_switchOn(television);
}

//override 
void _OnCommand_delete(Command* self){
  assert(self != NULL);
  OnCommand* object = (OnCommand*) self;  // downcast
  assert(object->television != NULL);
  Television_delete(object->television);
  Command_log("Deallocating OnCommand %lx\n", self);
  free(object);
}

Command* OnCommand_new(Television* television){
  assert(television != NULL);
  OnCommand* object = (OnCommand*) malloc(sizeof(OnCommand));
  assert(object != NULL);
  Command_log("Allocating new OnCommand %lx\n", object);
  Command* base = (Command*) object;      // upcast
  base->refcount = 1;
  base->execute = _OnCommand_execute;
  base->delete= _OnCommand_delete;
  object->television = Television_copy(television); // shared ownership
  return  base;
}

/******************************************************************************/
/*                                  OffCommand                                 */
/******************************************************************************/

typedef struct OffCommand_ OffCommand;

struct OffCommand_ {
  Command base;
  Television* television;
};

// override 
void _OffCommand_execute(Command* self){
  assert(self != NULL);
  OffCommand* object = (OffCommand*) self;  // downcast
  Television* television = object->television;
  assert(television != NULL);
  Television_switchOff(television);
}

//override 
void _OffCommand_delete(Command* self){
  assert(self != NULL);
  OffCommand* object = (OffCommand*) self;  // downcast
  assert(object->television != NULL);
  Television_delete(object->television);
  Command_log("Deallocating OffCommand %lx\n", self);
  free(object);
}

Command* OffCommand_new(Television* television){
  assert(television != NULL);
  OffCommand* object = (OffCommand*) malloc(sizeof(OffCommand));
  assert(object != NULL);
  Command_log("Allocating new OffCommand %lx\n", object);
  Command* base = (Command*) object;      // upcast
  base->refcount = 1;
  base->execute = _OffCommand_execute;
  base->delete= _OffCommand_delete;
  object->television = Television_copy(television); // shared ownership
  return  base;
}


/******************************************************************************/
/*                                  UpCommand                                 */
/******************************************************************************/

typedef struct UpCommand_ UpCommand;

struct UpCommand_ {
  Command base;
  Television* television;
};

// override 
void _UpCommand_execute(Command* self){
  assert(self != NULL);
  UpCommand* object = (UpCommand*) self;  // downcast
  Television* television = object->television;
  assert(television != NULL);
  Television_volumeUp(television);
}

//override 
void _UpCommand_delete(Command* self){
  assert(self != NULL);
  UpCommand* object = (UpCommand*) self;  // downcast
  assert(object->television != NULL);
  Television_delete(object->television);
  Command_log("Deallocating UpCommand %lx\n", self);
  free(object);
}

Command* UpCommand_new(Television* television){
  assert(television != NULL);
  UpCommand* object = (UpCommand*) malloc(sizeof(UpCommand));
  assert(object != NULL);
  Command_log("Allocating new UpCommand %lx\n", object);
  Command* base = (Command*) object;      // upcast
  base->refcount = 1;
  base->execute = _UpCommand_execute;
  base->delete= _UpCommand_delete;
  object->television = Television_copy(television); // shared ownership
  return  base;
}


/******************************************************************************/
/*                                  DownCommand                                 */
/******************************************************************************/

typedef struct DownCommand_ DownCommand;

struct DownCommand_ {
  Command base;
  Television* television;
};

// override 
void _DownCommand_execute(Command* self){
  assert(self != NULL);
  DownCommand* object = (DownCommand*) self;  // downcast
  Television* television = object->television;
  assert(television != NULL);
  Television_volumeDown(television);
}

//override 
void _DownCommand_delete(Command* self){
  assert(self != NULL);
  DownCommand* object = (DownCommand*) self;  // downcast
  assert(object->television != NULL);
  Television_delete(object->television);
  Command_log("Deallocating DownCommand %lx\n", self);
  free(object);
}

Command* DownCommand_new(Television* television){
  assert(television != NULL);
  DownCommand* object = (DownCommand*) malloc(sizeof(DownCommand));
  assert(object != NULL);
  Command_log("Allocating new DownCommand %lx\n", object);
  Command* base = (Command*) object;      // upcast
  base->refcount = 1;
  base->execute = _DownCommand_execute;
  base->delete= _DownCommand_delete;
  object->television = Television_copy(television); // shared ownership
  return  base;
}




int Command_test(){
  //basic new/copy/delete
  printf("\nnew, copy, delete...\n");
  Television* tv = Television_new();
  Command* on1 = OnCommand_new(tv);
  Command* on2 = Command_copy(on1);
  Command_delete(on2);
  Command_delete(on1);
  Television_delete(tv);
  assert(!Command_hasMemoryLeak());
  // execute
  printf("\nexecute...\n");
  tv = Television_new();
  Command* on = OnCommand_new(tv);
  Command* off = OffCommand_new(tv);
  Command* up = UpCommand_new(tv);
  Command* down = DownCommand_new(tv);
  Command_execute(on);
  Command_execute(up);
  Command_execute(down);
  Command_execute(off);
  Command_delete(down);
  Command_delete(up);
  Command_delete(on);
  Command_delete(off);
  Television_delete(tv);
  assert(!Command_hasMemoryLeak());

  return 0;
}



/******************************************************************************/
/*                                   Main                                     */
/******************************************************************************/

// let's try it all out
int main(){
//  Television_test();
//  Command_test();

  // our application will need some reveiver object
  Television* device = Television_new();
  // our application will need an invoker object, which
  // in turns relies on concrete command objects:
  Command* on   = OnCommand_new(device);    // command to switch device on
  Command* off  = OffCommand_new(device);   // command to switch device off
  Command* up   = UpCommand_new(device);    // command to turn volume up
  Command* down = DownCommand_new(device);  // command to turn volume down
  // now we are ready to create our invoker object which
  // we should think of as some sort of application menu.
  RemoteControl menu;
  RemoteControl_init(&menu, on, off, up, down);
  // client code is now able to access the invoker object
  RemoteControl_switchPowerOn(&menu);
  RemoteControl_raiseVolume(&menu);
  RemoteControl_raiseVolume(&menu);
  RemoteControl_raiseVolume(&menu);
  RemoteControl_lowerVolume(&menu);
  RemoteControl_switchPowerOff(&menu);
  // heap clean up
  RemoteControl_destroy(&menu);
  Television_delete(device);
  assert(!Command_hasMemoryLeak());
  return 0;
}



