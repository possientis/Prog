(load "exp-type.scm")

(define (eval-defined? exp env)
  (if (not (variable? exp))
    #f
    ((env 'defined?) exp)))

    





