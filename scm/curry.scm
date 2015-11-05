(define (curry f)
  (lambda (x)
    (lambda (y) (f x y))))

