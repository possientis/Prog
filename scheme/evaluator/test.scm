(require 'macro)

(load "main.scm")                 ; define lazy-eval

(strict-eval '(load "main.scm"))  ; global-env also has 'strict-eval now 

(define-syntax do-run
  (syntax-rules ()
    ((do-run expr)
     (force-thunk (lazy-eval 'expr)))))

(do-run (strict-eval '(load "lazy.scm")))

(display (do-run (analyze-eval '(lazy?))))(newline)


(exit 0)

 
