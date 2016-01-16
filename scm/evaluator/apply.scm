(define (exp-operator exp) (car exp))
(define (exp-operands exp) (cdr exp))

(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)                       ; TBI
         (apply-primitive-procedure procedure arguments))       ; TBI
        ((compound-procedure? procedure)                        ; TBI
         (eval-sequence
           (procedure-body procedure)                           ; TBI
           (extend-environment                                  ; TBI
             (procedure-parameters procedure)                   ; TBI
             arguments
             (procedure-environment procedure))))               ; TBI
        (else (error "Unknown procedure type -- APPLY" procedure))))



