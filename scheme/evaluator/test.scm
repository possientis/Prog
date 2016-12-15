(load "main.scm")

(set-debug #f)

(define expr '((lambda arg (apply + arg)) 1 2 3 4 5))



(define x (analyze-eval expr))
(display "x = ")(display (force-thunk x))(newline)


(exit 0)
