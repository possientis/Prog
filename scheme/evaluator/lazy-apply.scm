;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-apply)) 
  (begin
    (define included-lazy-apply #f)
    (display "loading lazy-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (lazy-apply proc-thunk args)
  (debug "check6: proc-thunk = ")(debug proc-thunk)(debug-newline)
  (debug "check7: args = ")(debug args)(debug-newline)
  (let ((proc (force-thunk proc-thunk)))
    (debug "check8: proc = ")(debug proc)(debug-newline)
    (cond ((primitive-procedure? proc)  (lazy-apply-primitive-procedure proc args))
          ((eval-procedure? proc)       (lazy-apply-eval-procedure proc args))
          ((analyze-procedure? proc)    (lazy-apply-analyze-procedure proc args))
          (else (error "Unknown procedure type -- LAZY-APPLY" proc)))))

))  ; include guard




