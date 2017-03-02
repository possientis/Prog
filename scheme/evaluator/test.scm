(load "main.scm")
(load "tools.scm")

(define expr '((lambda arg (apply + arg)) 1 2 3 4 5))

(define t (lazy-eval expr))

(display "thunk = ")(display t)(newline)

(force-thunk t)

(exit 0)
