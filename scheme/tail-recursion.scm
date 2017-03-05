(define (foo n)
  (display "n = ")(display n)(newline)
  (foo (1+ n)))

(foo 0)


