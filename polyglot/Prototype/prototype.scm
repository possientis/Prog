; Prototype design pattern
; Imagine that in order to instantiate certain objects we need to carry out
; expensive database queries. In order to improve performance, it would 
; be beneficial to cache whatever object is created from the database
; and return a copy of the cached object whenever a subsequent request
; for object instantiation arises.

(require 'hash-table)

(define Cloneable     ; constructor
  (let ((static_ #f)) ; dummy field, achieves name encapsulation and readability
    ; object built from data is a message passing interface
    (define (this data) ; data ignored here
      (lambda (m)  
        (cond ((eq? m 'clone) (display "Cloneable::clone is not implemented\n"))
        (else (display "Cloneable: unknown operation error\n")))))
    ; returning no argument constructor
    (lambda () (this 'ignored))))

(define Shape
  (let ((static_ #f)) ; dummy field, achieves name encapsulation and readability
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'getID) (getID data))
              ((eq? m 'setID) (setID data))
              ((eq? m 'draw)(display "Shape::draw is not implemented\n"))
              ((eq? m 'clone)(display "Shape::clone is not implemented\n"))
              (else ((base data) m))))); calling operation on base object
    (define (getID data)
      (car data)) ; data expected to be the pair (ID,base)
    (define (setID data)
      (lambda (val) (set-car! data val)))
    (define (base data)
      (cdr data)) ; data expected to be the pair (ID, base)
    ; returning no argument constructor
    (lambda () (this (cons #f (Cloneable)))))) ; ID = #f , base = (Cloneable)

(define Rectangle ; constructor
  (let ((static_ #f)) ; dummy field, achives name encapsulation and readability
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'draw) (draw data))
              ((eq? m 'clone)(clone data))
              (else ((base data) m))))) ; calling operation on base object
    (define (draw data)
      (display "Inside Rectangle::draw() method.\n")) ; data ignored
    (define (clone data)
      (let ((new (Rectangle)))  ;instantiating new rectangle 
        ((new 'setID) (data 'getID))  ; data is simply base object
        new)) ;returning clone
    (define (base data) ; data is simply base object
      data)
    ; returning no argument constructor
    (lambda () (this (Shape)))))  ; data is simply base object

(define Square ; constructor
  (let ((static_ #f)) ; dummy field, achieves name encapsulation and readability
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'draw) (draw data))
              ((eq? m 'clone)(clone data))
              (else ((base data) m))))) ; calling operation on base object
    (define (draw data)
      (display "Inside Square::draw() method.\n")) ; data ignored
    (define (clone data)
      (let ((new (Square)))  ;instantiating new rectangle 
        ((new 'setID) (data 'getID))  ; data is simply base object
        new)) ;returning clone
    (define (base data) ; data is simply base object
      data)
    ; returning no argument constructor
    (lambda () (this (Shape)))))  ; data is simply base object

(define Circle ; constructor
  (let ((static_ #f)) ; dummy field, achieves name encapsulation and readability
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'draw) (draw data))
              ((eq? m 'clone)(clone data))
              (else ((base data) m))))) ; calling operation on base object
    (define (draw data)
      (display "Inside Circle::draw() method.\n")) ; data ignored
    (define (clone data)
      (let ((new (Circle)))  ;instantiating new rectangle 
        ((new 'setID) (data 'getID))  ; data is simply base object
        new)) ;returning clone
    (define (base data) ; data is simply base object
      data)
    ; returning no argument constructor
    (lambda () (this (Shape)))))  ; data is simply base object

(define PrototypeManager  ; constructor
  (let ((static_ #f)) ; dummy field, achieves name encapsulation and readability
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'getShape)(getShape data))
              ((eq? m 'loadCache)(loadCache data))
              (else (display "PrototypeManager: unknown operation error\n")))))
    (define (getShape data)
      (lambda (key) (hash-table-get data key)))  ; data is simply a hash-table

    (define (loadCache data)
      (let ((rect (Rectangle)))
        ((rect 'setID) "1")
        (hash-table-set data (rect 'getID) rect)) ; data is simply hash-table
      (let ((square_ (Square))) ; Scheme case insensitive, care with names
        ((square_ 'setID) "2")
        (hash-table-set data (square_ 'getID) square_))
      (let ((circle_ (Circle))) 
        ((circle_ 'setID) "3")
        (hash-table-set data (circle_ 'getID) circle_)))
    ; needed to interact with hash-table
    (define hash-table-get (hash-inquirer equal?))
    (define hash-table-set (hash-associator equal?))
    ; returning no argument constructor
    (lambda () (this (make-hash-table 10)))))


; need a prototype manager
(define manager (PrototypeManager))
; prototype manager registers a few prototypes
(manager 'loadCache)
; prototype manager can now be used as a factory object
(define clonedShape1 ((manager 'getShape) "1"))
(clonedShape1 'draw)

(define clonedShape2 ((manager 'getShape) "2"))
(clonedShape2 'draw)

(define clonedShape3 ((manager 'getShape) "3"))
(clonedShape3 'draw)

(exit 0)

