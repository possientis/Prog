; Proxy Design Pattern
;
; This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
; https://www.youtube.com/watch?v=XvbDqLrnkmA

; A proxy is a class which functions as an interface to something else

; There are three participants to the proxy design pattern:
;
; 1. subject
; 2. real subject
; 3. proxy
;

; The subject is the common interface between the real object and proxy
; the real object is that which the proxy is meant to be substituted for

(define component-price-virtual-table   ; constructor
  (let ((let-for-name-encapsulation 'anything))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'cpu-price) (cpu-price data))
              ((eq? m 'ram-price) (ram-price data))
              ((eq? m 'ssd-price) (ssd-price data))
              (else (error "component-price: unknown operation" m)))))
    ;
    (define (cpu-price data) (cadr data))
    (define (ram-price data) (caddr data))
    (define (ssd-price data) (cadddr data))
    ;
    ; returning three arguments constructor
    ;
    (lambda (cpu ram ssd) (this (list 'data cpu ram ssd)))))

; default value of virtual table argument expected by component-price constructor
(define component-price-vt
  (let ((cpu (lambda (data) (error "cpu-price is not implemented")))
        (ram (lambda (data) (error "ram-price is not implemented")))
        (ssd (lambda (data) (error "ssd-price is not implemented"))))
    (component-price-virtual-table cpu ram ssd)))

(define stored-component-price-vt
  (let ((cpu (lambda (data) 250.0))
        (ram (lambda (data) 32.0))
        (ssd (lambda (data) 225.0)))
    (component-price-virtual-table cpu ram ssd)))

; data layout for object is expected to be (list 'data base-object this)
; i.e. (caddr data) is a reference to object itself
(define proxy-component-price-vt
  (let ((cpu (lambda (data) (request-from-server 'cpu)))
        (ram (lambda (data) (request-from-server 'ram)))
        (ssd (lambda (data) (request-from-server 'ssd))))
    (component-price-virtual-table cpu ram ssd)))

; this is the subject
(define component-price     ; constructor
  (let ((let-for-name-encapsulation 'anything))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (let ((virtual-table (cadr data)))
          ((virtual-table m) data))))
    ;
    ; returning constructor with optional argument
    ;
    (lambda arg
      (cond ((null? arg)        ; no argument, returning component-price instance 
             (this (list 'data component-price-vt)))
            ((null? (cdr arg))  ; single argument, returning derived object
             (this (list 'data (car arg)))) ; (car arg) is virtual table
            (else (error "too many arguments in constructor component-price"))))))

; this is the real subject
(define stored-component-price  ; constructor
  (lambda () (component-price stored-component-price-vt)))

; this is the proxy
(define proxy-component-price   ; constructor
  (lambda () (component-price proxy-component-price-vt)))

; NOTE: we are being inconsistent with the implementations of this exercise 
; in other languages, as we do not make 'request-from-server' an instance
; member of the class proxy-component-price. In fact, there was no reason to 
; make it an instance member as it has no dependency to the internals of
; the instance, so it should have been declared static instead.

(define (request-from-server request)
  (((server 'get-instance) 'send-request) request))


(define server              ; constructor
  (let ((let-for-name-encapsulation 'anything))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'send-request) (send-request data))
              (else (error "server: unknown operation" m)))))
    ;
    (define (to-string request)
      (cond ((eq? request 'cpu) "CPU")
            ((eq? request 'ram) "RAM")
            ((eq? request 'ssd) "SSD")))
    ;
    (define (send-request data)
      (lambda (request)
        (display "Server receiving request for ")
        (display (to-string request))(display " price\n")
        ; In our example, server uses real subject
        (let ((component (stored-component-price))) ; real-subject
          (display "Server respondiing to request for ")
          (display (to-string request))(display " price\n")
          (cond ((eq? request 'cpu) (component 'cpu-price))
                ((eq? request 'ram) (component 'ram-price))
                ((eq? request 'ssd) (component 'ssd-price))
                (else (error "invalid server request" request))))))
    ;
    (define _server #f) ; to initialized
    ;
    (define (start-server) 
      (set! _server (this 'data))
      (display "Component price server running, awaiting request\n"))
    ;
    (define static-interface
      (lambda arg
        (if (null? arg)         ; no argument, simply returning server instance 
          (this 'data)
          (let ((m (car arg)))  ; otherwise, static call 
            (cond ((eq? m 'get-instance) _server)
                  ((eq? m 'start-server) (start-server))
                  (else (error "server: invalid static member" m)))))))
    ;
    ; simply returning static interface
    ;
    static-interface))


(server 'start-server)
; we can use proxy as if it was real, making client code a lot simpler
(define prices (proxy-component-price))
(let ((cpu (prices 'cpu-price))
      (ram (prices 'ram-price))
      (ssd (prices 'ssd-price)))
  (display "The CPU price is ")(display cpu)(newline)
  (display "The RAM price is ")(display ram)(newline)
  (display "The SSD price is ")(display ssd)(newline))

(exit 0)
