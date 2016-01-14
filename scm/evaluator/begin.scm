(define (begin? exp) (tagged-list? exp 'begin)) 

(define (begin-actions exp) (cdr exp))





