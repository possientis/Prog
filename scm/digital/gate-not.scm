(load "transistor.scm")

(define (gate-not in out earth power)
  (p-transistor in power out)
  (n-transistor in earth out))

