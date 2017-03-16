(define (even? n)
  (cond ((zero? n) #t)
        (else (odd? (1- n)))))

(define (odd? n)
  (cond ((zero? n) #f)
        (else (even? (1- n)))))


(display (even? 10000000))(newline)
(display (odd?  10000000))(newline)

(exit 0)
