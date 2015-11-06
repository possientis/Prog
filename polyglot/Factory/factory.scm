(define (IShape hook)
  ; interface
  (define (this m)
    (cond ((eq? m 'draw) (hook))
          (else (display "IShape: unkwown operation error\n"))))
  ; returning interface
  this)

(define (Rectangle)
  (define this (IShape (lambda () (display "Inside Rectangle::draw() method.\n"))))
  ; returning interface
  this)

(define (Square)
  (define this (IShape (lambda () (display "Inside Square::draw() method.\n"))))
  ; returning interface
  this)

(define (Circle)
  (define this (IShape (lambda () (display "Inside Circle::draw() method.\n"))))
  ; returning interface
  this)


(define (ShapeFactory)
  ; interface
  (define (this m)
    (cond ((eq? m 'getShape) getShape)
          (else (display "ShapeFactory: unknown operation error\n"))))
  ; private member
  (define (getShape shapeType)
    (cond ((equal? shapeType "") #f)
          ((equal? (string-upcase shapeType) "CIRCLE") (Circle))
          ((equal? (string-upcase shapeType) "RECTANGLE") (Rectangle))
          ((equal? (string-upcase shapeType) "SQUARE") (Square))
          (else #f)))
  ; returning interface
  this)

(define factory (ShapeFactory))

; get an object of Circle and call its draw method.
(define shape1 ((factory 'getShape) "CIRCLE"))
(shape1 'draw)

; get an object of Rectangle and call its draw method.
(define shape2 ((factory 'getShape) "RECTANGLE"))
(shape2 'draw)

; get an object of Square and call its draw method.
(define shape3 ((factory 'getShape) "SQUARE"))
(shape3 'draw)

(exit 0)








