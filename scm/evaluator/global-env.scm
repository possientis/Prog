(load "primitive.scm")
(load "environment.scm")

(define (setup-environment)
  (let ((initial-env
          (((environment) 'extended)
           (primitive-procedure-names)
           (primitive-procedure-objects))))
    initial-env))

(define global-env (setup-environment))

;(display (global-env 'to-string))(newline)


