;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-apply)) 
  (begin
    (define included-lazy-apply #f)
    (display "loading lazy-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (lazy-apply proc args)
  (cond ((primitive-procedure? proc) (lazy-apply-primitive-procedure proc args))
        ((eval-procedure? proc) (lazy-apply-eval-procedure proc args))
        ((analyze-procedure? proc) (lazy-apply-analyze-procedure proc args))
        (else (error "Unknown procedure type -- LAZY-APPLY" proc))))

))  ; include guard




