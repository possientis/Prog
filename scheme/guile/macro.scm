;(require 'macro)     ; uncomment for scm

(define-syntax when
  (syntax-rules ()
    ((when condition exp ...)
     (if condition 
       (begin exp ...)))))

(when #t
  (display "hey ho\n")
  (display "let's go\n"))

(display 
(let-syntax ((unless
               (syntax-rules ()
                 ((unless condition exp ...)
                  (if (not condition)
                    (begin exp ...))))))
  (unless #t (exit 1))
  "rock rock rock")
)

(newline)
(display
(letrec-syntax ((my-or
                  (syntax-rules ()
                    ((my-or)
                     #t)
                    ((my-or exp)
                     exp)
                    ((my-or exp rest ...)
                     (let ((t exp))
                       (if t
                          t
                          (my-or rest ...)))))))
  (my-or #f "rockaway beach"))
)

(exit 0)
