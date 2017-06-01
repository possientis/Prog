(require 'macro)

(load "main.scm")                 ; define lazy-eval

(strict-eval '(load "main.scm"))  ; global-env also has 'strict-eval now 


(define-syntax run
  (syntax-rules ()
    ((run expr)
     (force-thunk (lazy-eval '(strict-eval 'expr))))))

(run (load "lazy.scm"))

(display (force-thunk (lazy-eval '(strict-eval '(lazy?)))))(newline)



(exit 0)


