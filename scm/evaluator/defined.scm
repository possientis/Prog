(load "exp-type.scm")

(define (defined?-variable exp) (cadr exp))

(define (eval-defined? exp env)
  (let ((variable (defined?-variable exp))) 
    (if (not (variable? variable)) #f  ((env 'defined?) variable)))) 


    





