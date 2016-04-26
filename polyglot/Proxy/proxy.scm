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

; This is the subject
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

; this virtual table expects object data to be have format
; (list 'data virtual-table this), so (caddr data) is a reference to the object
(define proxy-component-price-vt
  (let ((this (lambda (data) (caddr data))))
    (let ((cpu (lambda (data) (((this data) 'request-from-server) 'cpu)))
          (ram (lambda (data) (((this data) 'request-from-server) 'ram)))
          (ssd (lambda (data) (((this data) 'request-from-server) 'ssd))))
      (component-price-virtual-table cpu ram ssd))))

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

(define proxy-component-price   ; constructor
  (let ((let-for-name-encapsulation 'anything))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'request-from-server) (request-from-server-data))
              (else ...




