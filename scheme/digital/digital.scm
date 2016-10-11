(load "wire.scm")
(load "source.scm")
(load "connect.scm")
(load "transistor.scm")
(load "gate-nand.scm")

(newline)
(display "####################################################################\n")
(display "                    DIGITAL SIMULATOR                               \n")
(display "####################################################################\n")
(newline)

(global 'debug-false!)  ; additional output for debugging purposes

(newline)
(display "setting up new wires a b c d e f g\n")
(define a (wire))
(define b (wire))
(define c (wire))
(define d (wire))
(define e (wire))
(define f (wire))
(define g (wire))

(newline)
(display "setting probes on wires\n")
(begin ((a 'set-tag!) 'a)(a 'probe!))
(begin ((b 'set-tag!) 'b)(b 'probe!))
(begin ((c 'set-tag!) 'c)(c 'probe!))
(begin ((d 'set-tag!) 'd)(d 'probe!))
;(begin ((e 'set-tag!) 'e)(e 'probe!))
;(begin ((f 'set-tag!) 'f)(f 'probe!))
;(begin ((g 'set-tag!) 'g)(g 'probe!))
(newline)

;; power supply
((e 'set-signal!) #f 'x)
((g 'set-signal!) #t 'x)


;; creating RS-Latch
(gate-nand a d c e g)
(gate-nand b c d e g)


((a 'set-signal!) #f 'x)
((b 'set-signal!) #t 'x)
(global 'propagate!)
(display "time = ")
(display (global 'now))
(newline)
((a 'set-signal!) #t 'x)
((b 'set-signal!) #f 'x)
(global 'propagate!)
(display "time = ")
(display (global 'now))
(newline)
((a 'set-signal!) #t 'x)
((b 'set-signal!) #t 'x)
(global 'propagate!)
(display "time = ")
(display (global 'now))
(newline)


