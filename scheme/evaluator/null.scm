(load "main.scm")
(load "do-run.scm")

(do-run 
  '(display "program starting ..."))

(do-run
  '(define x '()))

(newline)(newline)

(define t (make-thunk '(not (null? x)) global-env))

(display "x = ")(display ((global-env 'lookup) 'x))(display " : --> ")(display (force-thunk ((global-env 'lookup) 'x)))(newline)

(display "thunk? : ")(display (thunk? t))(newline)
(display "evaluated?: ") (display (thunk-evaluated? t)) (newline)
(display "expression: ") (display (thunk-expression t))(newline)
(display "environment null?: ")(display (null? (thunk-environment t)))(newline)
(display "value: ")(display (thunk-value t))(newline)

(display "(strict-eval '(not (null? x))) = ")
(display (strict-eval '(not (null? x)) global-env))
(newline)

(display "(strict-eval 'x) = ")
(display (strict-eval 'x global-env))
(newline)

(display "(strict-eval '(null? x)) = ")
(display (strict-eval '(null? x) global-env))
(newline)

(newline)(newline)


(do-run
  '(display "program terminating ..."))

(newline)

(exit 0)

