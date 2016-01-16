(load "make.scm") ; make-lambda

(define (let-bindings exp) (cadr exp))
(define (let-body exp) (cddr exp))
(define (let-parameters exp) (map car (let-bindings exp)))
(define (let-operands exp) (map cadr (let-bindings exp)))

(define (let->combination exp)
  (cons (make-lambda (let-parameters exp) (let-body exp)) (let-operands exp)))


