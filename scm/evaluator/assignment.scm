(define (assignment-variable exp) (cadr exp))

(define (assignment-expression exp) (caddr exp))

(define (eval-assignment exp env)
  (set-variable-value! 
    (assignment-variable exp)
    (eval (assignment-expression exp) env)  
    env))

(define (set-variable-value! var val env)
  ((env 'set!) var val))

; added for analyze
; the assignment expresssion can be analyzed just once
(define (analyze-assignment exp)
  (let ((var (assignment-variable exp))
        (vproc (analyze (assignment-expresssion exp))))
    (lambda (env) (set-variable-value! var (vproc env) env))))

