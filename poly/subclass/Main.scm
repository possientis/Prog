#!/usr/bin/scm
(load "A.scm")
(load "B.scm")

(define (Main)
  (define x (A 1))  ; Scheme code is not case sensitive 'x' and not 'a'
  (define y (B 2 3))
  (display (x 'aGet))(display ":")(display (y 'aGet))
  (display ":")(display (y 'b))(newline)
  (x 'foo)
  (y 'foo)
  (let ((c (B 4 5)))  ; cannot use 'define' again
    (c 'foo))
  (let ((a1 (A x)) (b1 (B y)))
     (display (a1 'aGet))(display ":")(display (b1 'aGet))
     (display ":")(display (b1 'b))(newline))
  (exit 0))


(Main)

