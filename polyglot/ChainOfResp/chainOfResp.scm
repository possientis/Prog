; Chain of Responsibility Design Pattern

; The Chain Of Responsibility design pattern is meant to decouple
; clients (which may have various requests) from request handlers
; which may be of different types. Rather than forcing a client
; to have the precise knowledge of which request handler is able
; to deal with which type of request, the Chain of Responsibility
; design pattern creates a common base interface to all request
; handlers, and unites them into a single linked list (a 'chain').
; Now the client only needs to know the head of the chain, to
; which it sends all of its requests. Each request handler, apart
; from maintaining a link to a 'successor', fundamentally has
; a 'handleRequest' method which now accepts all types of request.
; However, when faced with a request which it cannot fulfill, a 
; request handler will pass on the request to its successor. 
; Provided the chain of request handlers is properly set up, all
; requests should be handled appropriately.
;
; Note that this pattern can be generalized from 'chains' to non
; linear structure between objects, such as trees. One can imagine
; a network of request handlers, which are either dealing with 
; request themselves, or passing requests to other (linked) 
; request handlers
;
; This coding exercise is meant to provide a simulation of an ATM
; machine. As a server, the machine is able to provide a service
; 'getAmount' to an external client which consists in the delivery
; of the appropriate set of bank notes which corresponds to a 
; desired amount. As a client, the ATM machine relies on various
; request handlers, namely those which are specialized in the delivery
; of specific bank notes. So the machine relies on a service for the 
; delivery of $5 notes, another service for the delivery of $10 notes
; and so forth. This is a case where the Chain of Responsibility 
; design pattern can be succesfully applied, allowing the implementation 
; of the ATM machine to forget about all those different services and 
; the details of how to convert an amount of cash into a set of notes.
;
;
; Our ATM machine only need to worry about the head of the chain of
; services, which it maintains as an internal data member. This machine
; has the ability to provide a set of bank notes from a desired amount

(define atm-machine   ; constructor
  (let ((let-for-name-encapsulation 'anything))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'get-amount) (get-amount data))
              (else (error "atm-machine: unknown operation" m)))))
    ;
    (define (get-amount data)
      (lambda (amount)
        (display "ATM machine: requesting amount of $")
        (display amount)(newline)
        (((handler data) 'handle-request) amount))) ; delegates request to chain
    ;
    (define (handler data) (cadr data)) ; data = ('data handler)
    ;
    ; returning no argument constructor
    ;
    (lambda ()
      (let ((handler (request-handler 'get-handling-chain)))
        (this (list 'data handler))))))


; This is the base class, uniting all request handlers into a common
; interface. This class in normally abstract (the whole point of the
; design pattern is dealing with multiple types of request).
(define request-handler ; constructor
  (let ((let-for-name-encapsulation 'anything))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'handle-request) (handle-request data))
              ((eq? m 'denomination)   (denomination data))
              (else (error "request-handler: unknown operation" m)))))
    ; 
    (define (denomination data) (cadr data))  ; data = ('data denomination next)
    ;
    (define (next data) (caddr data))
    ;
    (define (handle-request data)
      (lambda (amount)
        (let* ((denom (denomination data))
               (value (denom 'value))
               (succ  (next data)))
          (cond ((< amount 0) (error "handle-request: amount should be >= 0"))
                ((= amount 0) '())  ; empty list
                ((not (= (modulo amount 5) 0)) 
                (error "handle-request: amount should be multiple of $5"))
                ((>= amount value)
                 (cons denom ((handle-request data) (- amount value)))); recursive
                ((not (eq? succ #f)) ((succ 'handle-request) amount)) ; passing on
                (else (error "handle-request: chain is badly set up"))))))
    ;
    (define interface ; possible static calls or instance creation
      (lambda arg
        (cond ((null? arg)(error "request-handler: expects at least one argument"))
              ((null? (cdr arg))  ; one argument passed, static call
               (let ((m (car arg)))
                 (cond ((eq? m 'get-handling-chain) (get-handling-chain))
                       (else (error "request-handler: illegal static call")))))
              (else (let ((denom (car arg)) (successor (cadr arg)))
                      ; simply returning object instance
                      (this (list 'data denom successor)))))))
    ;
    (define (get-handling-chain)
      (request-handler-for-fifty 
        (request-handler-for-twenty
          (request-handler-for-ten
            (request-handler-for-five #f)))))
    ;
    ; returning interface
    ;
    interface))

; delivers $50 notes
(define (request-handler-for-fifty next)
  (request-handler (banknote 'fifty) next))


; delivers $20 notes
(define (request-handler-for-twenty next)
  (request-handler (banknote 'twenty) next))


; delivers $10 notes
(define (request-handler-for-ten next)
  (request-handler (banknote 'ten) next))


; delivers $5 notes
(define (request-handler-for-five next)
  (request-handler (banknote 'five) next))

(define banknote    ; constructor
  (let ((let-for-name-encapsulation 'anything))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'value) (value data))
              ((eq? m 'to-string) (to-string data))
              (else (error "banknote: unknown operation" m)))))
    ;
    (define (value data)
      (let ((type (cadr data)))
        (cond ((eq? type 'five)     5)
              ((eq? type 'ten)      10)
              ((eq? type 'twenty)   20)
              ((eq? type 'fifty)    50)
              (else (error "banknote: unknown type" type)))))
    ;
    (define (to-string data) (number->string (value data)))
    ;
    ; returning single argument constructor
    ;
    (lambda (type) (this (list 'data type)))))
              
(define (print-note-list note-list)
  (display "[")
  (let loop ((l note-list)(start-flag #t))
    (if (null? l) 
      (display "]")
      ; else
      (begin
        (if (not start-flag) (display ", "))
        (display ((car l) 'to-string))
        (loop (cdr l) #f)))))
      
; main
(define atm (atm-machine))
(define note-list ((atm 'get-amount) 235))
(display "The notes handed out by the ATM machine are:\n")
(print-note-list (reverse note-list))
(newline)
(exit 0)



