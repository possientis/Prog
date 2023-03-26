(define (IShape hook)
; Abstract Factory design pattern (define (IShape hook)
  ; interface
  (define (this m)
    (cond ((eq? m 'draw) (hook))
          (else (display "IShape: unkwown operation error\n"))))
  ; returning interface
  this)

(define (AbstractShape hook)
  ; data
  (define base (IShape hook))
  (define mColor #f)
  ; interface
  (define (this m)
    (cond ((eq? m 'setColor) setColor)
          ((eq? m 'color) mColor)
          ((eq? m 'asString) asString)
          (else (base m))))
  ; methods
  (define (setColor color)
    (set! mColor color))
  ;
  (define (asString color)
    (cond ((eq? color 'RED) "red")
          ((eq? color 'GREEN) "green")
          ((eq? color 'BLUE) "blue")
          (else "unknown color")))
  ; returning interface
  this)

(define (Rectangle color)
  ; method
  (define (draw)
    (display "Drawing ")
    (display ((this 'asString) (this 'color)))
    (display " rectangle\n"))
  ; interface
  (define this (AbstractShape draw))
  ; initialization
  ((this 'setColor) color)
  ; returning interface
  this)

(define (Square color)
  ; method
  (define (draw)
    (display "Drawing ")
    (display ((this 'asString) (this 'color)))
    (display " square\n"))
  ; interface
  (define this (AbstractShape draw))
  ; initialization
  ((this 'setColor) color)
  ; returning interface
  this)

(define (Circle color)
  ; method
  (define (draw)
    (display "Drawing ")
    (display ((this 'asString) (this 'color)))
    (display " circle\n"))
  ; interface
  (define this (AbstractShape draw))
  ; initialization
  ((this 'setColor) color)
  ; returning interface
  this)

; using the template method pattern here, as the actual
; behaviour of 'getShape' will be defined via specialization
; of virtual method getColor through subclassing
(define (AbstractShapeFactory object)
  (define self object)  ; need to keep track of concrete object
  ; interface
  (define (this m)
    (cond ((eq? m 'getColor)(getColor))
          ((eq? m 'getShape) getShape)
          (else (display "AbstractShapeFactory: unknown operation error\n"))))
  ; methods
  (define (getColor)
    (display "AbstractShapeFactory: getColor() not implemented\n"))
  (define (getShape shapeType)
    (cond ((equal? shapeType "") #f)
          ((equal?(string-upcase shapeType)"CIRCLE")(Circle(self 'getColor)))
          ((equal?(string-upcase shapeType)"RECTANGLE")(Rectangle(self 'getColor)))
          ((equal? (string-upcase shapeType) "SQUARE") (Square (self 'getColor)))
          (else #f)))
  ; returning interface
  this)

(define (RedShapeFactory)
  ;interface
  (define (this m)
    (cond ((eq? m 'getColor) (getColor))
          (else (base m))))
  (define base (AbstractShapeFactory this)) 
  ; method
  (define (getColor)
    'RED)
  ; returning interface
  this)

(define (GreenShapeFactory)
  ;interface
  (define (this m)
    (cond ((eq? m 'getColor) (getColor))
          (else (base m))))
  (define base (AbstractShapeFactory this)) 
  ; method
  (define (getColor)
    'GREEN)
  ; returning interface
  this)

(define (BlueShapeFactory)
  ;interface
  (define (this m)
    (cond ((eq? m 'getColor) (getColor))
          (else (base m))))
  (define base (AbstractShapeFactory this)) 
  ; method
  (define (getColor)
    'BLUE)
  ; returning interface
  this)

(define (FactoryProducer)
  ; interface
  (define (this m)
    (cond ((eq? m 'getFactory) getFactory)
          (else (display "FactoryProducer: unknown operation error\n"))))
  ; method
  (define (getFactory factoryType)
    (cond ((equal? factoryType "") #f)
          ((equal? (string-upcase factoryType) "RED")(RedShapeFactory))
          ((equal? (string-upcase factoryType) "GREEN")(GreenShapeFactory))
          ((equal? (string-upcase factoryType) "BLUE")(BlueShapeFactory))
          (else #f)))
  ; returning interface
  this)

(define producer (FactoryProducer))
; producing set of red widgets
(define redFactory ((producer 'getFactory) "Red"))
(define shape1 ((redFactory 'getShape) "CIRCLE"))
(define shape2 ((redFactory 'getShape) "RECTANGLE"))
(define shape3 ((redFactory 'getShape) "SQUARE"))
(shape1 'draw)
(shape2 'draw)
(shape3 'draw)

; producing set of green widgets
(define greenFactory ((producer 'getFactory) "Green"))
(define shape4 ((greenFactory 'getShape) "CIRCLE"))
(define shape5 ((greenFactory 'getShape) "RECTANGLE"))
(define shape6 ((greenFactory 'getShape) "SQUARE"))
(shape4 'draw)
(shape5 'draw)
(shape6 'draw)

; producing set of blue widgets
(define blueFactory ((producer 'getFactory) "Blue"))
(define shape7 ((blueFactory 'getShape) "CIRCLE"))
(define shape8 ((blueFactory 'getShape) "RECTANGLE"))
(define shape9 ((blueFactory 'getShape) "SQUARE"))
(shape7 'draw)
(shape8 'draw)
(shape9 'draw)

(exit 0)

