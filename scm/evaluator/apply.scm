(load "environment.scm")
(load "primitive.scm")
(load "compound.scm")
(load "operands.scm")

(define (exp-operator exp) (car exp))
(define (exp-operands exp) (cdr exp))

(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)                       
         (apply-primitive-procedure procedure arguments))       
        ((compound-procedure? procedure)                        
         (eval-sequence
           (procedure-body procedure)                           
           (((procedure-environment procedure) 'extended)
              (procedure-parameters procedure)                   
              arguments)))
        (else (error "Unknown procedure type -- APPLY" procedure))))



