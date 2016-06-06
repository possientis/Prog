;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-apply)) 
  (begin
    (define included-apply #f)
    (display "loading apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "environment.scm")
(load "primitive.scm")
(load "exp-type.scm")
(load "compound.scm")
(load "operands.scm")

; destructuring
(define (exp-operator exp) (car exp))
(define (exp-operands exp) (cdr exp))

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
        (params (proecdure-parameters proc))
        (init-env (procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (body extended-env))))

(define (eval-application exp env)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (eval operator env))
          (args (list-of-values operands env)))
      (apply proc args))))



; added for analyze
(define (analyze-application exp)
  (let ((fproc (analyze (exp-operator exp)))
        (aprocs (map analyze (exp-operands exp))))
    (lambda (env)
      (execute-application (fproc env)
                           (map (lambda (aproc) (aproc env)) aprocs)))))

; when 'analyzing' a lambda expression, we call 'make-procedure' with a body
; which is not the same body as that used as argument when 'evaluating'. Our
; new body is an 'analyzed' body, namely a map expecting an environment as 
; argument. This explains why 'execute-application' needs to be different
; from a simple 'apply'

(define (execute-application procedure arguments)
;  (display "execute-application:\tprocedure = ")(display procedure)(newline) 
;  (display "execute-application:\targuments = ")(display arguments)(newline) 
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((eval-procedure? procedure)  ; TODO
         ((procedure-body procedure)
          (((procedure-environment procedure) 'extended)
           (procedure-parameters procedure)
           arguments)))
        (else (error "Unknown procedure type -- EXECUTE-APPLICATION" procedure))))

))  ; include guard

