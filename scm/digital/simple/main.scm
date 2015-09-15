(load "wire.scm")

(define a (wire))
(define b (wire))

(display "setting probes on wires a and b\n")
(probe a 'a)
(probe b 'b)
(display "connecting a and b to inverter\n")
(gate-not a b)
(display "running time simulation...\n")
(schedule 'propagate!)



