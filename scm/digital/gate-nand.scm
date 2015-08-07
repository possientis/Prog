(load "transistor.scm")

(define (gate-nand in-0 in-1 out earth power)
  (let ((aux (wire)))
    (n-transistor in-0 earth aux)
    (n-transistor in-1 aux out)
    (p-transistor in-0 power out)
    (p-transistor in-1 power out)))
