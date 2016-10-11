(load "transistor.scm")

(define (gate-nor in-0 in-1 out earth power)
  (let ((aux (wire)))
    (p-transistor in-0 power aux)
    (p-transistor in-1 aux out)
    (n-transistor in-0 earth out)
    (n-transistor in-1 earth out)))
