(load "main.scm")

(define-syntax run
  (syntax-rules ()
    ((run expr ...)
     (strict-eval '(strict-eval '(begin expr ...))))))

(set-debug-level 1)

(strict-eval '(load "main.scm"))

(display "interpreter successfully loaded...\n")

(run (+ 1 1)) 



(exit 0)
