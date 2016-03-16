(define (assignment-variable exp) (cadr exp))

(define (assignment-expression exp) (caddr exp))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-expression exp) env)  
                       env)
  'ok)

(define (set-variable-value! var val env)
  ((env 'set!) var val))


