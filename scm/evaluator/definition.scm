(load "make.scm") ; make-lambda

(define (definition-variable exp)
  (if (symbol? (cadr exp)) (cadr exp) (caadr exp)))

(define (definition-expression exp)
  (if (symbol? (cadr exp))
    (caddr exp)
    (make-lambda (cdadr exp)                                   
                 (cddr exp))))

(define (eval-definition exp env)
  ((env 'define!) (definition-variable exp)
                  (eval (definition-expression exp) env))           
  'ok)


