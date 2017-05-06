(require 'macro)

(load "main.scm")                 ; define lazy-eval

(strict-eval '(load "main.scm"))  ; global-env also has 'strict-eval now 

(define-syntax do-run
  (syntax-rules ()
    ((do-run expr)
     (strict-eval expr))))


(exit 0)

 
