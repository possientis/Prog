; need to investigate null.scm before coming back to this

(load "main.scm")
(load "do-run.scm")

(do-load "main.scm")
(do-load "tools.scm")

(do-run '(display "thunk...\n"))
(do-run '(define t (make-thunk '(+ 1 1) global-env)))

(define expr 't)
(define value1 ((global-env 'lookup) expr))
(define value2 (make-thunk '(+1 1) global-env))


(display "expression: ")(display expr)(newline)
(display "variable?: ")(display (variable? expr))(newline)
(display "apply?: ")(display (equal? expr 'apply))(newline)
(display "eval?: ")(display (equal? expr 'eval))(newline)
(display "load?: ")(display (equal? expr 'load))(newline)
(display "map?: ")(display (equal? expr 'map))(newline)

(newline)(display "value1: ")(display value1)(newline)
(newline)(display "value2: ")(display value2)(newline)(newline)

(display "==========================================================\n")
(display "Native scheme interprets both value1 and value2 as thunks.\n")
(display "However a thunk is a list of the form (thunk obj) where obj\n")
(display "is a native scheme object (specifically a native scheme \n")
(display "procedure). Although value1 is of form (thunk data), the \n")
(display "second component data **is not** a native scheme procedure.\n")
(display "------------>  So value1 **is not** a thunk  <------------\n")
(display "it is wrongly recognized as such by the interpreter.\n")
(display "==========================================================\n")
(newline)

(display "(thunk? value1): ")(display (thunk? value1))(newline)
(display "(thunk? value2): ")(display (thunk? value2))(newline)



(strict-eval-variable 't global-env)


(exit 0)
