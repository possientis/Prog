;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-apply)) 
  (begin
    (define included-new-apply #f)
    (display "loading new-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (new-apply proc args)
  (cond ((primitive-procedure? proc)  (apply-primitive-procedure proc args))
        ((eval-procedure? proc)       (apply-eval-procedure proc args))
        ((analyze-procedure? proc)    (apply-analyze-procedure proc args))
        (else (error "Unknown procedure type -- APPLY" proc))))

))  ; include guard

