(load "make.scm")

(define (named-let? exp)
  (and (tagged-list? exp 'let) (symbol? (cadr exp)))) ; not a regular 'let'

(define (named-let-variable exp) (cadr exp))

(define (named-let-bindings exp) (caddr exp))

(define (named-let-body exp) (cdddr exp))

(define (named-let-parameters exp) (map car (named-let-bindings exp)))

(define (named-let-operands exp) (map cadr (named-let-bindings exp)))

(define (named-let-function exp)
  (make-lambda (named-let-parameters exp) (named-let-body exp)))

(define (named-let-definition exp)
  (list 'define (named-let-variable exp) (named-let-function exp)))

(define (named-let-function-call exp)
  (cons (named-let-variable exp) (named-let-parameters exp)))

(define (named-let->combination exp)
  (cons (make-lambda (named-let-parameters exp) 
                     (list (named-let-definition exp) 
                           (named-let-function-call exp))) 
        (named-let-operands exp)))

