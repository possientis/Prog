(load "true-false.scm")

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp) 
  (if (not (null? (cdddr exp)))
    (cadddr exp)
    '#f)) ; returning expression '#f, not the value #f

(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))                     
    (eval (if-consequent exp) env)                             
    (eval (if-alternative exp) env)))                          

