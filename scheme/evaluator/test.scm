(require 'macro)

(load "main.scm")                 ; define lazy-eval

(strict-eval '(load "main.scm"))  ; global-env also has 'strict-eval now 

(define-syntax do-run
  (syntax-rules ()
    ((do-run expr)
     (force-thunk (lazy-eval 'expr)))))

(do-run (let ((file (open-file "and.scm" "r")))
          (let ((code (read file)))
            (close-port file)
            (display code)
            'ok)))


(exit 0)


