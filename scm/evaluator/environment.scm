(load "environment1")
(load "environment2")
; required interface for environment
;
; - lookup var      -> val
; - set! var val    -> void
; - define! var val -> void
; - extended        -> env
; - display         -> env
;

(define (environment) (environment2)) ; choose implementation here


