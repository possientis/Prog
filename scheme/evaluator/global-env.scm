;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-global-env)) 
  (begin
    (define included-global-env #f)
    (display "loading global-env")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "primitive.scm")
(load "primitive-procedure.scm")
(load "environment.scm")

(debug "running global-env.scm ...")(debug-newline)

(define (setup-environment)
  (debug "setting up environment ...")(debug-newline)
  (let ((initial-env
          (((environment) 'extended)
           (primitive-procedure-names)
           (primitive-procedure-objects))))
    (debug "environment setup is complete.")(debug-newline)
    initial-env))

(debug "defined 'setup-environment successfully ...")(debug-newline)



(define global-env (setup-environment))

(debug "defined 'global-env succesfully ...")(debug-newline) 

(define (global-env-reset!)
  (set! global-env (setup-environment)))


))  ; include guard

