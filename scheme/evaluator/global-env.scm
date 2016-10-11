;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-global-env)) 
  (begin
    (define included-global-env #f)
    (display "loading global-env")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "primitive.scm")
(load "primitive-procedure.scm")
(load "environment.scm")

(define (setup-environment)
  (let ((initial-env
          (((environment) 'extended)
           (primitive-procedure-names)
           (primitive-procedure-objects))))
    initial-env))

(define global-env (setup-environment))

;(display (global-env 'to-string))(newline)

))  ; include guard

