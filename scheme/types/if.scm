(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp) (cadddr exp))

(define (evaluate-if exp)
  (let ((pred (evaluate (if-predicate exp))))
    (if pred
      (evaluate (if-consequent exp))
      (evaluate (if-alternative exp)))))
  
