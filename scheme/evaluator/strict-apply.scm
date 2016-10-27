;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-apply)) 
  (begin
    (define included-strict-apply #f)
    (display "loading strict-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (strict-apply proc args)
  (cond ((primitive-procedure? proc) (strict-apply-primitive-procedure proc args))
        ((eval-procedure? proc)      (strict-apply-eval-procedure proc args))
        ((analyze-procedure? proc)   (strict-apply-analyze-procedure proc args))
        (else (error "Unknown procedure type -- STRICT-APPLY" proc))))

))  ; include guard




