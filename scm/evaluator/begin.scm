(define (begin? exp) (tagged-list? exp 'begin)) 

(define (begin-actions exp) (cdr exp))

(define (make-begin operands) (cons 'begin operands))



