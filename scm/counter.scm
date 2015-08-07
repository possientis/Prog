(define (counter)
  (let ((n 0))
    (lambda ()
      (set! n (+ n 1))
      n)))


(define (counter2)
  (apply
    (lambda (n)
      (lambda ()
        (set! n (+ n 1))
        n))
    '(0)))

