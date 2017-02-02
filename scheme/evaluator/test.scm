; need to investigate null.scm before coming back to this

(load "main.scm")
(load "do-run.scm")


(do-load "primitive.scm")           ; interpreter running file
(do-load "primitive-procedure.scm") ; interpreter running file
(do-load "environment.scm")         ; interpreter running file

(do-run                             ; interpreter running code
  '(define (setup-environment)
     (let ((initial-env
             (((environment) 'extended)
              (primitive-procedure-names)
              (primitive-procedure-objects))))
       initial-env)))


(do-run '(define base-env (environment)))

(do-run '(define extend-proc (base-env 'extended)))

(do-run '(define proc-names (primitive-procedure-names)))

(do-run '(define proc-objects (primitive-procedure-objects)))

(do-run '(display extend-proc))

(newline)
(newline)
(do-run '(display proc-names))

(newline)
(newline)
(do-run '(display proc-objects))

(newline)
(newline)
(do-run '(extend-proc proc-names proc-objects))


(exit 0)
