; Command Design Pattern
(ns command (:gen-class))
; from https://en.wikipedia.org/wiki/Command_pattern 
; In object-oriented programming, the command pattern is a behavioral 
; design pattern in which an object is used to encapsulate all information 
; needed to perform an action or trigger an event at a later time. This 
; information includes the method name, the object that owns the method 
; and values for the method parameters.
;
; Four terms always associated with the command pattern are command, 
; receiver, invoker and client. A command object knows about receiver 
; and calls a method of the receiver. Values for parameters of the 
; receiver method are stored in the command. The receiver then does 
; the work. An invoker object knows how to execute a command, and 
; optionally does bookkeeping about the command execution. The invoker 
; does not know anything about a concrete command, it knows only about 
; command interface. Both an invoker object and several command objects 
; are held by a client object. The client decides which commands to 
; execute at which points. To execute a command, it passes the command 
; object to the invoker object.
;
; Using command objects makes it easier to construct general components 
; that need to delegate, sequence or execute method calls at a time of 
; their choosing without the need to know the class of the method or the 
; method parameters. Using an invoker object allows bookkeeping about 
; command executions to be conveniently performed, as well as implementing 
; different modes for commands, which are managed by the invoker object, 
; without the need for the client to be aware of the existence of 
; bookkeeping or modes.

(defmulti execute :type)
; This is the Command interface
(def Command    ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :execute) (execute data)
               :else (throw 
                       (Exception. (format "Command: unknown operation %s" m))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [data] (this data))))

(defmethod execute ::command [data]
  (throw (Exception. "Command::execute is abstract")))

; This is the Invoker class. It is akin to the remote control of an 
; electronic device, or a menu object within an application. It allows
; the client perform actions through a single interface, without
; having to worry about the various part of a system. The invoker class
; it itself very generic and is unaware if the specifics of commands.
(def RemoteControl  ; constructor
  (letfn
    ;
    [(switchPowerOn   [data]  ((:powerOn data)    :execute))
     (switchPowerOff  [data]  ((:powerOff data)   :execute))
     (raiseVolume     [data]  ((:volumeUp data)   :execute))
     (lowerVolume     [data]  ((:volumeDown data) :execute))
     ; object created from data is message passing interface
     (this [data]
       (fn [m]
         (cond (= m :switchPowerOn)   (switchPowerOn data)
               (= m :switchPowerOff)  (switchPowerOff data)
               (= m :raiseVolume)     (raiseVolume data)
               (= m :lowerVolume)     (lowerVolume data)
               :else (throw
                       (Exception. (format "RemoteControl: unknown operation %s"
                                           m))))))]
    ;
    ; returning four arguments constructor
    ;
    (fn [on off up down]
      (this { :powerOn on :powerOff off :volumeUp up :volumeDown down }))))

; This is the receiver class. It is the class of objects which will perform
; the various actions. There may be sereral receiver classes comprising
; a system, and the invoker object may invoke commands which applies
; to many different receivers. Typically a menu will execute actions 
; involving not just the application object, but many other sub-objects 
; As this is a simple coding exercise with one receiver object, their
; seems to be a correspondance between the interface of the RemoteControl
; and that of the Televion. However, this correspondance is misleading
; as in general, the interface of the invoker object may have little in
; common with those of the various receiver objects.
(def Television   ; constructor
  (letfn
    ;
    [(switchOn [data]
      (if (= @(data :isOn) false)
        (do (dosync (ref-set (data :isOn) true))
            (println "Television is now switched on"))))
    ;
    (switchOff [data]
      (if (= @(data :isOn) true)
        (do (dosync (ref-set (data :isOn) false))
            (println "Television is now switched off"))))
    ;
    (volumeUp [data]
      (if (and (= @(data :isOn) true) (< @(data :volume) 20))
        (do (dosync (alter (data :volume) inc))
            (println "Television volume increased to" @(data :volume)))))
    ;
    (volumeDown [data]
      (if (and (= @(data :isOn) true) (> @(data :volume) 0))
        (do (dosync (alter (data :volume) dec))
            (println "Television volume decreased to" @(data :volume)))))
    ; object created from data is message passing interface
    (this [data]
      (fn [m]
        (cond (= m :switchOn)   (switchOn data)
              (= m :switchOff)  (switchOff data)
              (= m :volumeUp)   (volumeUp data)
              (= m :volumeDown) (volumeDown data)
              :else (throw
                      (Exception. 
                        (format "Television: unknown operation %s" m))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] (this { :isOn (ref false) :volume (ref 10) }))))


; These are the concrete command objects. These commands have exact
; knowledge of receiver objects as well as which methods and argument
; should be used when issuing a request to receiver objects.
; As can be seen, the command design pattern relies on a fair amount
; of indirection: client code will call an invoker object (menu, remote)
; which will in turn execute a command, which will send a request to
; to a receiver object, which will finally perform the requested action.
(def OnCommand
  (fn [television]
    (Command {:type ::on-command :television television})))
(derive ::command ::on-command)
(defmethod execute ::on-command [data] ((:television data) :switchOn))

(def OffCommand
  (fn [television]
    (Command {:type ::off-command :television television})))
(derive ::command ::off-command)
(defmethod execute ::off-command [data] ((:television data) :switchOff))

(def UpCommand
  (fn [television]
    (Command {:type ::up-command :television television})))
(derive ::command ::up-command)
(defmethod execute ::up-command [data] ((:television data) :volumeUp))

(def DownCommand
  (fn [television]
    (Command {:type ::down-command :television television})))
(derive ::command ::down-command)
(defmethod execute ::down-command [data] ((:television data) :volumeDown))

; let's try it all out
(defn -main []
  ; our application will need some reveiver object
  (let [device  (Television)
        ; our application will need an invoker object, which
        ; in turns relies on concrete command objects:
        on      (OnCommand    device) ; command to switch device on
        off     (OffCommand   device) ; command to switch device off
        up      (UpCommand    device) ; command to turn volume up
        down    (DownCommand  device) ; command to turn volume down
        ; now we are ready to create our invoker object which
        ; we should think of as some sort of application menu.
        menu    (RemoteControl on off up down)]
    ; client code is now able to access the invoker object
    (menu :switchPowerOn)
    (menu :raiseVolume)
    (menu :raiseVolume)
    (menu :raiseVolume)
    (menu :lowerVolume)
    (menu :switchPowerOff)))

;(-main)
