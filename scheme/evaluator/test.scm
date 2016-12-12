(load "main.scm")

(set-debug #t)

(define expr '((lambda arg (apply + arg)) 1 2 3 4 5))

(define proc (lazy-eval 'apply))


(define x (lazy-eval expr))


(exit 0)
