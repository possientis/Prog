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
  execute :: a -> IO()

-- This is the Invoker class. It is akin to the remote control of an 
-- electronic device, or a menu object within an application. It allows
-- the client perform actions through a single interface, without
-- having to worry about the various part of a system. The invoker class
-- it itself very generic and is unaware if the specifics of commands.

data RemoteControl a b c d = RemoteControl {  
  powerOn :: a, powerOff :: b, volumeUp :: c, volumeDown :: d
}
                                               
switchPowerOn :: (Command a) => RemoteControl a b c d -> IO ()
switchPowerOn remote = execute (powerOn remote)


switchPowerOff :: (Command b) => RemoteControl a b c d -> IO ()
switchPowerOff remote = execute (powerOff remote)

raiseVolume :: (Command c) => RemoteControl a b c d -> IO ()
raiseVolume remote = execute (volumeUp remote)

lowerVolume :: (Command d) => RemoteControl a b c d -> IO ()
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

data Television  = Television { volume:: Int, isOn:: Bool, buffer:: String }

data TV a = TV (Television -> (a, Television))

run :: TV a -> Television -> (a, Television)
run (TV f) television = f television

instance Monad TV where
  return a = TV (\state -> (a, state))
  k >>= f  = TV (\state -> let (x, newState) = run k state in run (f x) newState) 

switchOnTV :: TV () 
switchOnTV  = TV (
  \state -> case isOn state of
              True  -> ((), state)
              False -> ((), Television 
                (volume state) 
                True
                ((buffer state) ++ "Television is now switched on"))) 
                                            

switchOffTV :: TV () 
switchOffTV  = TV (
  \state -> case isOn state of
              False -> ((), state)
              True  -> ((), Television 
                (volume state) 
                False
                ((buffer state) ++ "Television is now switched off")))

volumeUpTV :: TV () 
volumeUpTV  = TV (
  \state -> case isOn state of
              False -> ((), state)
              True  -> ((), Television 
                newVolume 
                True 
                ((buffer state) 
                  ++ "Television volume increased to" ++ (show newVolume))) 
                    where newVolume = (volume state) + 1)

volumeDownTV :: TV () 
volumeDownTV  = TV (
  \state -> case isOn state of
              False -> ((), state)
              True  -> ((), Television 
                newVolume 
                True 
                ((buffer state) 
                  ++ "Television volume decreased to" ++ (show newVolume))) 
                    where newVolume = (volume state) - 1)


