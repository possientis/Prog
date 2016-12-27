(load "main.scm")

(set-debug #t)

(define x (make-thunk 3 '()))

(display "x = ")(display x)(newline)

(exit 0)
