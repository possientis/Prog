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
           (extend-environment                      
             (procedure-parameters procedure)                   
             arguments
             (procedure-environment procedure))))               
        (else (error "Unknown procedure type -- APPLY" procedure))))



