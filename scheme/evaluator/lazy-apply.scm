;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-apply)) 
  (begin
    (define included-lazy-apply #f)
    (display "loading lazy-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (lazy-apply proc-thunk args)
  (display "check6: proc-thunk = ")(display proc-thunk)(newline)
  (display "check7: args = ")(display args)(newline)
  (let ((proc (force-thunk proc-thunk)))
    (display "check8: proc = ")(display proc)(newline)
    (cond ((primitive-procedure? proc)  (lazy-apply-primitive-procedure proc args))
          ((eval-procedure? proc)       (lazy-apply-eval-procedure proc args))
          ((analyze-procedure? proc)    (lazy-apply-analyze-procedure proc args))
          (else (error "Unknown procedure type -- LAZY-APPLY" proc)))))

))  ; include guard




