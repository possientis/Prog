; need to investigate null.scm before coming back to this

(load "main.scm")
(load "do-run.scm")

(do-load "main.scm")
(do-load "tools.scm")

(do-run '(display "thunk...\n"))
(do-run '(let ((t (make-thunk '(+ 1 1) global-env)))
           (assert-equals (thunk? t) #t "thunk.1")))

(exit 0)
