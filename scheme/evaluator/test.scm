(load "main.scm")

(set-debug #t)

(define expr '((lambda arg (apply + arg)) 1 2 3 4 5))

(define x (lazy-eval expr))

(display "x = ")(display y)(newline)

(exit 0)
