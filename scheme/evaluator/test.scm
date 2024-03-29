(require 'macro)

(load "main.scm")                 ; define lazy-eval

;(strict-eval '(load "main.scm"))  ; global-env also has 'strict-eval now 

(define-syntax do-run
  (syntax-rules ()
    ((do-run expr ...)
     (force-thunk (lazy-eval '(begin expr ...))))))

(do-run 
  (load "dictionary-test.scm")
  (dictionary-test "frame3.scm" 'frame3)
  (newline))


(exit 0)

 
