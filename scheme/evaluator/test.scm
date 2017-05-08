(require 'macro)

(load "main.scm")                 ; define lazy-eval

(strict-eval '(load "main.scm"))  ; global-env also has 'strict-eval now 

(define-syntax do-run
  (syntax-rules ()
    ((do-run expr ...)
     (force-thunk (lazy-eval '(strict-eval '(begin expr ...)))))))

(do-run (load "lazy.scm"))
(do-run (display (lazy?))(newline))


(exit 0)

 
