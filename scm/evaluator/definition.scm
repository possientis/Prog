(load "make.scm")

(define (definition? exp) (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp)) (cadr exp) (caadr exp)))

(define (definition-expression exp)
  (if (symbol? (cadr exp))
    (caddr exp)
    (make-lambda (cdadr exp)                                   
                 (cddr exp))))

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)                   ; TBI 
                    (eval (definition-expression exp) env)           
                    env)
  'ok)



