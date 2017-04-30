(require 'macro)

(load "main.scm")                 ; define lazy-eval

(strict-eval '(load "main.scm"))  ; global-env also has 'strict-eval now 


(define-syntax do-run
  (syntax-rules ()
    ((do-run expr)
     (force-thunk (lazy-eval '(strict-eval 'expr))))))


(do-run (load "and.scm"))






(exit 0)


