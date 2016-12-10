;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-apply)) 
  (begin
    (define included-lazy-apply #f)
    (display "loading lazy-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (lazy-apply proc-thunk args)
  (let ((proc (force-thunk proc-thunk)))
    (debug "\nlazy-apply: proc = ")(debug proc)(debug-newline)
    (debug "lazy-apply: args = ")(debug args)(debug-newline)
    (cond ((primitive-procedure? proc)  
           (debug "lazy-apply: calling lazy-apply-primitive-procedure ...\n")
           (lazy-apply-primitive-procedure proc args))
          ((eval-procedure? proc)       
           (debug "lazy-apply: calling lazy-apply-eval-procedure ...\n")
           (lazy-apply-eval-procedure proc args))
          ((analyze-procedure? proc)    
           (debug "lazy-apply: calling lazy-apply-analyze-procedure ...\n")
           (lazy-apply-analyze-procedure proc args))
          (else (error "Unknown procedure type -- LAZY-APPLY" proc)))))

))  ; include guard




