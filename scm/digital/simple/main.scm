(load "wire.scm")

(define a (wire))
(define b (wire))

(gate-not a b)
(schedule 'propagate!)


