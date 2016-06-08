;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-apply)) 
  (begin
    (define included-apply #f)
    (display "loading apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "exp-type.scm")
(load "environment.scm")
(load "primitive.scm")
(load "compound.scm")
(load "operands.scm")

; safeguarding the primitive procedure 'apply' before redefining it
(define apply-in-underlying-scheme apply)
; now redefining
(define (apply proc args)
  (cond ((primitive-procedure? proc) (apply-primitive-procedure proc args))       
        ((eval-procedure? proc) (apply-eval-procedure proc args))
        ((analyze-procedure? proc) (apply-analyze-procedure proc args))
        (else (error "Unknown procedure type -- APPLY" proc))))


(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme (primitive-implementation proc) args)) 

(define (apply-eval-procedure proc args)
  (let ((body (procedure-body proc))
        (params (procedure-parameters proc))
        (init-env (procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (eval-sequence body extended-env))))

(define (apply-analyze-procedure proc args)
  (let ((body (procedure-body proc))
        (params (procedure-parameters proc))
        (init-env (procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (body extended-env))))

))  ; include guard

