; Bridge design pattern

; bridge implementation interface
(define DrawAPI           ; constructor
  (let ((_static #f))     ; dummy 'let' field for name encapsulation
    ; object built from data is a message passing interface
    (define (this data)   ; data ignored here
      (lambda (m)
        (cond ((eq? m 'drawCircle) (drawCircle data))
              (else (display "DrawAPI: unknown operation error\n")))))
    (define (drawCircle data)
      (lambda (radius x y)
        (display "DrawAPI::drawCircle is not implemented\n")))
    ; returning no argument constructor
    (lambda() (this 'ignored))))

; concrete bridge implementation classes implementing DrawAPI interface
(define RedCircle         ; constructor
  (let ((_static #f))     ; dummy 'let' field for name encapsulation
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'drawCircle) (drawCircle data))
              (else ((base data) m)))))   ; passing message to base object
    (define (base data)
      data)               ; data is simply base object here
    (define (drawCircle data)
      (lambda (radius x y)
        (display "Drawing Circle[ color: red  , radius: ")
        (display radius)
        (display ", x: ")(display x)
        (display ", y: ")(display y)
        (display "]\n")))
    ; returning no argument constructor
    (lambda() (this (DrawAPI))))) ; data is base object

(define GreenCircle         ; constructor
  (let ((_static #f))     ; dummy 'let' field for name encapsulation
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'drawCircle) (drawCircle data))
              (else ((base data) m)))))   ; passing message to base object
    (define (base data)
      data)               ; data is simply base object here
    (define (drawCircle data)
      (lambda (radius x y)
        (display "Drawing Circle[ color: green, radius: ")
        (display radius)
        (display ", x: ")(display x)
        (display ", y: ")(display y)
        (display "]\n")))
    ; returning no argument constructor
    (lambda() (this (DrawAPI))))) ; data is base object


; create an abstract class Shape using the DrawAPI interface.
(define Shape             ; constructor
  (let ((_static #f))     ; dummy 'let' field for name encapsulation
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'draw) (draw data))
              ((eq? m 'drawAPI) (_drawAPI data))
              (else (display "Shape: unknown operation error\n")))))
    (define (_drawAPI data)
      data)               ; data is simply _drawAPI
    (define (draw data)
      (display "Shape::draw is not implemented\n"))
   ; returning one argument constructor
    (lambda(draw-api) (this draw-api))))  ; data is a DrawAPI object

; create concrete class implementing the Shape interface (abstract class)
(define Circle            ; constructor
  (let ((_static #f))     ; dummy 'let' field for name encapsulation
    ; object built from data is a message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'draw) (draw data))
              (else ((base data) 'm)))))  ; passing message to base object
    (define (base data)
      (car data))                         ; base object embedded as 'car'
    (define (draw data)
      (let ((draw-api ((car data) 'drawAPI))
            (x (cadr data))
            (y (caddr data))
            (radius (cadddr data)))
        ((draw-api 'drawCircle) radius x y)))
   ; returning four arguments constructor
    (lambda(x y radius draw-api) (this (list (Shape draw-api) x y radius)))))  

; Use Shape and DrawAPI classes to draw different colored circles
; implementation of concrete circles selected at run time.
(define red-circle (Circle 100 100 10 (RedCircle)))
(define green-circle (Circle 100 100 10 (GreenCircle)))
(red-circle 'draw)
(green-circle 'draw)

(exit 0)





