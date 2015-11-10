(define object
  (lambda data
    (lambda () data)))

(define (object-foo self)
  (car (self)))
(define (object-bar self)
  (cadr (self)))


(define x (object 4 5))
(display (object-foo x))(newline)
(display (object-bar x))(newline)




