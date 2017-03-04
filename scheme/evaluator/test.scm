(load "main.scm")
(load "tools.scm")

(define expr '((lambda arg (apply + arg)) 1 2 3 4 5))

(define t (lazy-eval expr))
(define e (thunk-expression t))

(display "expression =")(display e)(newline)

(define env (thunk-environment t))
(define s ((env 'lookup) 'arg))

(define arg (map force-thunk (force-thunk s)))

(display "arg = ")(display arg)(newline)

(define e2 '(apply + arg))

(define proc (strict-eval 'apply env))
(display "proc = ")(display proc)(newline)
(define args (map (lambda (x) (strict-eval x env)) '(+ arg)))
(define plus (car args))
(define l (cadr args)) 

(display "plus = ")(display plus)(newline)
(display "list = ")(display l)(newline)

(display (strict-apply-primitive-procedure plus l))(newline)


(display (force-thunk t))(newline)

(exit 0)
