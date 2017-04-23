(define (pred? exp) (tagged-list? exp 'pred))

(define (pred-expression exp) (cadr exp))

(define (evaluate-pred exp)
  (let ((value (evaluate (pred-expression exp))))
    (if (> value 0) 
      (- value 1)
      (error "Illegal call to 'pred' -- EVALUATE"))))
