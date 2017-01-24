;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-apply)) 
  (begin
    (define included-lazy-apply #f)
    (display "loading lazy-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (lazy-apply proc-thunk args)
  (debug "[DEBUG]: lazy-apply: proc-thunk = ")(debug proc-thunk)(debug-newline)
  (if (thunk? proc-thunk)
    (debug "[DEBUG]: lazy-apply: proc-thunk is a genuine thunk\n")
    (debug "[DEBUG]: lazy-apply: proc-thunk is not a genuine thunk\n"))
  (if (thunk? proc-thunk)
    (begin
      (if (thunk-evaluated? proc-thunk)
        (debug "[DEBUG]: lazy-apply: proc-thunk is already evaluated\n")
        (debug "[DEBUG]: lazy-apply: proc-thunk is not yet evaluated\n"))
      (if (null? (thunk-environment proc-thunk))
        (debug "[DEBUG]: lazy-apply: proc-thunk env is null\n")
        (debug "[DEBUG]: lazy-apply: proc-thunk is not null\n"))
      (debug "[DEBUG]: lazy-apply: thunk expression is ")
      (debug (thunk-expression proc-thunk))(debug-newline)
    ))
  (let ((proc (force-thunk proc-thunk)))
    (debug "[DEBUG]: lazy-apply: proc = ")(debug proc)(debug-newline)
    (cond ((primitive-procedure? proc) (lazy-apply-primitive-procedure proc args))
          ((eval-procedure? proc) (lazy-apply-eval-procedure proc args))
          ((analyze-procedure? proc) (lazy-apply-analyze-procedure proc args))
          (else (error "Unknown procedure type -- LAZY-APPLY" proc)))))

))  ; include guard




