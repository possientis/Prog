-- Command Design Pattern

-- from https://en.wikipedia.org/wiki/Command_pattern 
-- In object-oriented programming, the command pattern is a behavioral 
-- design pattern in which an object is used to encapsulate all information 
-- needed to perform an action or trigger an event at a later time. This 
-- information includes the method name, the object that owns the method 
-- and values for the method parameters.
--
-- Four terms always associated with the command pattern are command, 
-- receiver, invoker and client. A command object knows about receiver 
-- and calls a method of the receiver. Values for parameters of the 
-- receiver method are stored in the command. The receiver then does 
-- the work. An invoker object knows how to execute a command, and 
-- optionally does bookkeeping about the command execution. The invoker 
-- does not know anything about a concrete command, it knows only about 
-- command interface. Both an invoker object and several command objects 
-- are held by a client object. The client decides which commands to 
-- execute at which points. To execute a command, it passes the command 
-- object to the invoker object.
--
-- Using command objects makes it easier to construct general components 
-- that need to delegate, sequence or execute method calls at a time of 
-- their choosing without the need to know the class of the method or the 
-- method parameters. Using an invoker object allows bookkeeping about 
-- command executions to be conveniently performed, as well as implementing 
-- different modes for commands, which are managed by the invoker object, 
-- without the need for the client to be aware of the existence of 
-- bookkeeping or modes.

-- This is the Command interface
class Command a where
  execute :: a -> TV()

-- This is the Invoker class. It is akin to the remote control of an 
-- electronic device, or a menu object within an application. It allows
-- the client perform actions through a single interface, without
-- having to worry about the various part of a system. The invoker class
-- it itself very generic and is unaware if the specifics of commands.

data RemoteControl a b c d = RemoteControl {  
  powerOn :: a, powerOff :: b, volumeUp :: c, volumeDown :: d
}
                                               
switchPowerOn :: (Command a) => RemoteControl a b c d -> TV ()
switchPowerOn remote = execute (powerOn remote)


switchPowerOff :: (Command b) => RemoteControl a b c d -> TV ()
switchPowerOff remote = execute (powerOff remote)

raiseVolume :: (Command c) => RemoteControl a b c d -> TV ()
raiseVolume remote = execute (volumeUp remote)

lowerVolume :: (Command d) => RemoteControl a b c d -> TV ()
lowerVolume remote = execute (volumeDown remote)

-- This is the receiver class. It is the class of objects which will perform
-- the various actions. There may be sereral receiver classes comprising
-- a system, and the invoker object may invoke commands which applies
-- to many different receivers. Typically a menu will execute actions 
-- involving not just the application object, but many other sub-objects 
-- As this is a simple coding exercise with one receiver object, their
-- seems to be a correspondance between the interface of the RemoteControl
-- and that of the Televion. However, this correspondance is misleading
-- as in general, the interface of the invoker object may have little in
-- common with those of the various receiver objects.

data Television  = Television { volume:: Int, isOn:: Bool }

newTelevision :: Television
newTelevision = Television 10 False

data TV a = TV (Television -> IO (a, Television))

run :: TV a -> Television -> IO (a, Television)
run (TV f) television = f television

instance Monad TV where
  return a = TV (\state -> return (a, state))
  k >>= f  = TV (\state -> do   (x, newState) <- run k state 
                                run (f x) newState) 

switchOnTV :: TV () 
switchOnTV  = TV (
  \state -> case isOn state of
              True  -> return ((), state)
              False -> do putStrLn "Television is now switched on"
                          return ((), Television (volume state) True))
switchOffTV :: TV () 
switchOffTV  = TV (
  \state -> case isOn state of
              False -> return ((), state)
              True  -> do putStrLn "Television is now switched off"
                          return ((), Television (volume state) False))

volumeUpTV :: TV () 
volumeUpTV  = TV (
  \state -> case isOn state of
              False -> return ((), state)
              True  -> do putStrLn 
                            ("Television volume increased to "++(show newVolume))
                          return ((), Television newVolume True)
                            where newVolume = (volume state) + 1)
                          
volumeDownTV :: TV () 
volumeDownTV  = TV (
  \state -> case isOn state of
              False -> return ((), state)
              True  -> do putStrLn 
                            ("Television volume decreased to "++(show newVolume))
                          return ((), Television newVolume True)
                            where newVolume = (volume state) - 1)

-- These are the concrete command objects. These commands have exact
-- knowledge of receiver objects as well as which methods and argument
-- should be used when issuing a request to receiver objects.
-- As can be seen, the command design pattern relies on a fair amount
-- of indirection: client code will call an invoker object (menu, remote)
-- which will in turn execute a command, which will send a request to
-- to a receiver object, which will finally perform the requested action.
data OnCommand = OnCommand
instance Command OnCommand where
  execute OnCommand = switchOnTV 

data OffCommand = OffCommand
instance Command OffCommand where
  execute OffCommand = switchOffTV 

data UpCommand = UpCommand
instance Command UpCommand where
  execute UpCommand = volumeUpTV

data DownCommand = DownCommand
instance Command DownCommand where
  execute DownCommand = volumeDownTV

demo :: TV ()
demo = do
  let on    = OnCommand
  let off   = OffCommand
  let up    = UpCommand
  let down  = DownCommand
  let menu  = RemoteControl on off up down
  switchPowerOn  menu
  raiseVolume    menu
  raiseVolume    menu
  raiseVolume    menu
  lowerVolume    menu
  switchPowerOff menu


main :: IO ()
main = do 
  let device = newTelevision
  run demo device
  return ()







