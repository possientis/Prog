(define (f x)
  (define (even? n)
    (if (= n 0)
      #t
      (odd? (- n 1))))
  (define (odd? n)
    (if (= n 0)
      #f
      (even? (- n 1))))
  (if (even? x)
    (display "even")
    (display "odd"))
  (newline))


