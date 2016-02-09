; required interface for environment
;
; - empty?          -> bool
; - define! var val -> void
; - lookup var      -> val
; - set! var val    -> void
; - extended        -> env
; - display         -> env
;

; choose implementation here
(load "environment1")
(define environment environment1)


