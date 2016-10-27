;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-apply)) 
  (begin
    (define included-analyze-apply #f)
    (display "loading analyze-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (analyze-apply proc args)
  (cond ((primitive-procedure? proc) (analyze-apply-primitive-procedure proc args))
        ((eval-procedure? proc)      (analyze-apply-eval-procedure proc args))
        ((analyze-procedure? proc)   (analyze-apply-analyze-procedure proc args))
        (else (error "Unknown procedure type -- ANALYZE-APPLY" proc))))

))  ; include guard




