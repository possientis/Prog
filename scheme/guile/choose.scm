#!/usr/bin/guile \
-l fact2.scm -e main -s
!#

(define (choose n m)  ; n <= m
  (/ (fact m) (* (fact (- m n)) (fact n))))

(define (main args)
  (let ((n (string->number (cadr args)))
        (m (string->number (caddr args))))
    (display (choose n m))
    (newline)))
