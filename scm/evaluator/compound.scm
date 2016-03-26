(define (compound-procedure? procedure) (tagged-list? procedure 'procedure))

(define (procedure-parameters procedure) (cadr procedure))

(define (procedure-body procedure) (caddr procedure))

(define (procedure-environment procedure) (cadddr procedure))

