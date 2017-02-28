(load "main.scm")

(lazy-eval
  '(define (test)
     (display "+++test+++ is running\n")
     #f))

(display (lazy-eval '(test)))(newline)

(exit 0)
