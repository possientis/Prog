#!/usr/bin/guile \
-e main -s
!#

(define (fact n)
  (if (zero? n) 1
    (* n (fact (- n 1)))))

; now guile -l fact2.scm will succeed
(define (main args)
  (display (fact (string->number (cadr args))))
  (newline))
