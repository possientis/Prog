(define (evaluate exp)
  (cond ((true? exp)(evaluate-true exp))
        ((false? exp) (evaluate-false exp))
        ((if? exp) (evaluate-if exp))
        ((zero-exp? exp) (evaluate-zero exp))
        ((succ? exp) (evaluate-succ exp))
        ((pred? exp) (evaluate-pred exp))
        ((iszero? exp) (evaluate-iszero exp))
        (else (error "Unknown expression type -- EVALUATE"))))


