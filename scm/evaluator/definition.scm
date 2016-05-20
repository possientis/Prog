;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-definition)) 
  (begin
    (define included-definition #f)
    (display "loading definition")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "make.scm")

(define (definition-variable exp)
  (if (symbol? (cadr exp)) (cadr exp) (caadr exp)))

(define (definition-expression exp)
  (if (symbol? (cadr exp))
    (caddr exp)
    (make-lambda (cdadr exp)                                   
                 (cddr exp))))

(define (eval-definition exp env)
  ((env 'define!) (definition-variable exp)
                  (eval (definition-expression exp) env)))

; added for analyze
; the definition expression can be analyzed just once
(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (vproc (analyze (definition-expression exp))))
    (lambda (env) ((env 'define!) var (vproc env))))) 

))  ; include guard
