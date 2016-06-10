;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-apply)) 
  (begin
    (define included-apply #f)
    (display "loading apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "primitive-procedure.scm")
(load "eval-procedure.scm")
(load "analyze-procedure.scm")

; now redefining
(define (apply proc args)
  (cond ((primitive-procedure? proc) (apply-primitive-procedure proc args))       
        ((eval-procedure? proc) (apply-eval-procedure proc args))
        ((analyze-procedure? proc) (apply-analyze-procedure proc args))
        (else (error "Unknown procedure type -- APPLY" proc))))

))  ; include guard

