(load "environment.scm")
(load "primitive.scm")
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
        ((compound-procedure? procedure)                        
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

; added for analyze
(define (analyze-application exp)
  (let ((fproc (analyze (exp-operator exp)))
        (aprocs (map analyze (exp-operands exp))))
    (lambda (env)
      (execute-application (fproc env)
                           (map (lambda (aproc) (aproc env)) aprocs)))))

; need to understand why execute-application should differ from apply
