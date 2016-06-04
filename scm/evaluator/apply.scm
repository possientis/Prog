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

(define (exp-operator exp) (car exp))
(define (exp-operands exp) (cdr exp))

; safeguarding the primitive procedure 'apply' before redefining it
(define apply-in-underlying-scheme apply)
; now redefining
(define (apply procedure arguments)
;  (display "apply:\tprocedure = ")(display procedure)(newline)
;  (display "apply:\targuments = ")(display arguments)(newline)
  (cond ((primitive-procedure? procedure)                       
         (apply-primitive-procedure procedure arguments))       
        ((eval-procedure? procedure)  ; compound procedure, code not analyzed 
         (eval-sequence
           (procedure-body procedure)                           
           (((procedure-environment procedure) 'extended)
              (procedure-parameters procedure)                   
              arguments)))
        (else (error "Unknown procedure type -- APPLY" procedure))))

(define (apply-primitive-procedure proc args)
;  (display "apply-primitive-procedure:\tprocedure = ")(display proc)(newline)
;  (display "apply-primitive-procedure:\targuments = ")(display args)(newline)
;  (display "apply-primitive-procedure:\tprocedure-implementation = ")
;  (display (primitive-implementation proc))(newline)
  (apply-in-underlying-scheme (primitive-implementation proc) args)) 


(define (eval-application exp env)
  (apply (eval (exp-operator exp) env)
         (list-of-values (exp-operands exp) env)))



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

