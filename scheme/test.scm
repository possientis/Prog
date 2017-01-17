(define k #f)
(define (foo x y)
  (set! k (call-with-current-continuation identity))
  #f)

(let ((a 3) (b 4))
  (foo a b)
  #f)

(stack-trace k)

