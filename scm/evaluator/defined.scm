;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-defined)) 
  (begin
    (define included-defined #f)
    (display "loading defined")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "exp-type.scm")

(define (defined?-variable exp) (cadr exp))

(define (eval-defined? exp env)
  (let ((variable (defined?-variable exp))) 
    (if (not (variable? variable)) #f  ((env 'defined?) variable)))) 


;; added for analyze
(define (analyze-defined? exp)
  (let ((variable (defined?-variable exp)))
    (if (not (variable? variable))
      (lambda (env) #f)
      (lambda (env) ((env 'defined?) variable))))) 

))  ; include guard

    





