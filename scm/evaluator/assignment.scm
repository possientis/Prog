(define (assignment-variable exp) (cadr exp))

(define (assignment-expresssion exp) (caddr exp))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)                ; TBI
                       (eval (assignement-expression exp) env)  
                       env)
  'ok)


