(load "main.scm")
(load "do-run.scm")

(do-run 
  '(display "program starting ..."))

(do-run
  '(define x '()))

(do-run 
  '(display (not (null? x))))

(newline)(newline)

(define t (make-thunk '(not (null? x)) global-env))

(display "force-thunk:") (display (force-thunk t)) (newline)
(display "expression: ") (display (thunk-expression t))(newline)
(display "evaluated?: ") (display (thunk-evaluated? t)) (newline)
(display "environment null?: ")(display (null? (thunk-environment t)))(newline)
(display "thunk? : ")(display (thunk? t))(newline)

(newline)(newline)




(do-run
  '(display "program terminating ..."))

(newline)

