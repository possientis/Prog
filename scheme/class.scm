(require 'macro)

(define-syntax class
  (syntax-rules ()
    ((class name body ...)
     (define name
       (let ()
         body ...)))))

; test
(class point 
  (define (this data)
    (lambda (m)
      (cond ((eq? m 'x) (x data))
            ((eq? m 'y) (y data))
            (else (error "point: unknown operation:" m)))))
  ;
  (define (x data) (cadr data))
  ;
  (define (y data) (caddr data))
  ;
  ; returning two argument constructor
  ;
  (lambda (a b) (this (list 'data a b))))


(define p (point 3 5))
(display (p 'x))(newline)
(display (p 'y))(newline)

;(p 'foo) 


(class (foo x)
  ;
  (lambda (y) (+ x y)))

(define f (foo 6))

(display (f 7))(newline)




