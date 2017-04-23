(define (succ? exp) (tagged-list? exp 'succ))

(define (succ-expression exp) (cadr exp))

(define (evaluate-succ exp)
  (let ((value (evaluate (succ-expression exp))))
    (+ value 1)))
