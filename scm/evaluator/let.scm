(load "make.scm")

(define (let? exp)
  (and (tagged-list? exp 'let) (not (symbol? (cadr exp))))) ; is not named-let

(define (let-bindings exp) (cadr exp))
(define (let-body exp) (cddr exp))
(define (let-parameters exp) (map car (let-bindings exp)))
(define (let-operands exp) (map cadr (let-bindings exp)))

(define (let->combination exp)
  (cons (make-lambda (let-parameters exp) (let-body exp)) (let-operands exp)))


