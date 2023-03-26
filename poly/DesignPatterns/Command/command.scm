; Command Design Pattern

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

(define command
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'execute) (execute data))
              (else (error "command: unknown operation error" m)))))
    ;
    (define (execute data)
      (let ((virtual-method (cadr data))) ; data = ('data virtual-method ...
        (virtual-method data)))
    ;
    ; returning single argument constructor
    ;
    (lambda (data) (this data))))

; This is the Invoker class. It is akin to the remote control of an 
; electronic device, or a menu object within an application. It allows
; the client perform actions through a single interface, without
; having to worry about the various part of a system. The invoker class
; it itself very generic and is unaware if the specifics of commands.
(define remote-control  ; constructor
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'switch-power-on) (switch-power-on data))
              ((eq? m 'switch-power-off)(switch-power-off data))
              ((eq? m 'raise-volume)    (raise-volume data))
              ((eq? m 'lower-volume)    (lower-volume data))
              (else (error "remote-control: unknown operation error " m)))))
    ;
    (define (switch-power-on data)  ((on-power data) 'execute))
    (define (switch-power-off data) ((off-power data) 'execute))
    (define (raise-volume data)     ((volume-up data) 'execute))
    (define (lower-volume data)     ((volume-down data) 'execute))
    ;
    (define (on-power data)     (cadr data))
    (define (off-power data)    (caddr data))
    (define (volume-up data)    (cadddr data))
    (define (volume-down data)  (car (cddddr data)))
    ;
    ; returning four arguments contructor
    ;
    (lambda (on off up down) (this (list 'data on off up down)))))

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

(define television  ; constructor
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'switch-on)   (switch-on data))
              ((eq? m 'switch-off)  (switch-off data))
              ((eq? m 'volume-up)   (volume-up data))
              ((eq? m 'volume-down) (volume-down data)))))
    ;
    (define (on? data)    (cadr data))
    (define (volume data) (caddr data))
    ;
    (define (switch-on data)
      (if (not (on? data)) 
        (begin 
          (display "Television is now switched on\n")
          (set-car! (cdr data) #t))))
    ;
    (define (switch-off data)
      (if (on? data)
        (begin 
          (display "Television is now switched off\n")
          (set-car! (cdr data) #f))))
    ;
    (define (volume-up data)
      (if (on? data)
        (begin
        (set-car! (cddr data) (+ (volume data) 1))
        (display "Television volume increased to ")
        (display (volume data))(newline))))
    ;
    (define (volume-down data)
      (if (on? data)
        (begin
        (set-car! (cddr data) (- (volume data) 1))
        (display "Television volume decreased to ")
        (display (volume data))(newline))))
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (list 'data #f 10)))))


; These are the concrete command objects. These commands have exact
; knowledge of receiver objects as well as which methods and argument
; should be used when issuing a request to receiver objects.
; As can be seen, the command design pattern relies on a fair amount
; of indirection: client code will call an invoker object (menu, remote)
; which will in turn execute a command, which will send a request to
; to a receiver object, which will finally perform the requested action.


(define (on-command-override data)
  (let ((device (caddr data))) (device 'switch-on)))
(define (on-command device)
  (command (list 'data on-command-override device)))

(define (off-command-override data)
  (let ((device (caddr data))) (device 'switch-off)))
(define (off-command device)
  (command (list 'data off-command-override device)))

(define (up-command-override data)
  (let ((device (caddr data))) (device 'volume-up)))
(define (up-command device)
  (command (list 'data up-command-override device)))

(define (down-command-override data)
  (let ((device (caddr data))) (device 'volume-down)))
(define (down-command device)
  (command (list 'data down-command-override device)))

; let's try it all out
; our application will need some reveiver object
(let* ((device (television))
      ; our application will need an invoker object, which
      ; in turns relies on concrete command objects:
      (on      (on-command    device)) ; command to switch device on
      (off     (off-command   device)) ; command to switch device off
      (up      (up-command    device)) ; command to turn volume up
      (down    (down-command  device)) ; command to turn volume down
      ; now we are ready to create our invoker object which
      ; we should think of as some sort of application menu.
      (menu    (remote-control on off up down)))
        ; client code is now able to access the invoker object
        (menu 'switch-power-on)
        (menu 'raise-volume)
        (menu 'raise-volume)
        (menu 'raise-volume)
        (menu 'lower-volume)
        (menu 'switch-power-off))

(exit 0)




