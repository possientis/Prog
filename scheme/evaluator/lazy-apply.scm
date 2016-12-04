;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-apply)) 
  (begin
    (define included-lazy-apply #f)
    (display "loading lazy-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (lazy-apply proc-thunk args)
  (debug "\nlazy-apply: calling lazy-apply-eval-procedure\n")
  (let ((proc (force-thunk proc-thunk)))
    (cond ((primitive-procedure? proc)  (lazy-apply-primitive-procedure proc args))
          ((eval-procedure? proc)       (lazy-apply-eval-procedure proc args))
          ((analyze-procedure? proc)    (lazy-apply-analyze-procedure proc args))
          (else (error "Unknown procedure type -- LAZY-APPLY" proc)))))

))  ; include guard




