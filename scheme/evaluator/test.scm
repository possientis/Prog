; loading interpreter
(load "main.scm") 
(set-debug #t)

(force-thunk (lazy-eval '(load "main.scm")))
(force-thunk (lazy-eval '(load "tools.scm")))

(define sub-expr
  '(letrec
     ((loop (lambda (n) (if (= 0 n) 1 (* n (loop (- n 1)))))))
     (loop 5)))

(define expr (list 'test-expression sub-expr 120 "letrec.test"))

(force-thunk (lazy-eval expr))

(exit 0)


