(define (makeAdder param)
  (define (adder x)
    (+ x param))
  adder)
