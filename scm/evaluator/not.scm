(load "true-false.scm")

(define (not-predicate exp) (cadr exp))

(define (eval-not exp env)
  (if (true? (eval (not-predicate exp) env)) #f #t))  




