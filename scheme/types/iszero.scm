(define (iszero? exp) (tagged-list? exp 'zero?))

(define (iszero-expression exp) (cadr exp))

(define (evaluate-iszero exp)
  (let ((value (evaluate (iszero-expression exp))))
    (if (eq? 0 value) #t #f)))
