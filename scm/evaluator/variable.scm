(define (lookup-variable-value exp env)
  (cond ((eq? exp '+) '+)
        ((eq? exp '*) '*)
        ((eq? exp 'eval) 'eval)
        (else (error "Unbound variable -- EVAL" exp))))


