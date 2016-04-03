; required interface for environment
;
; - empty?          -> bool
; - define! var val -> void
; - lookup var      -> val
; - set! var val    -> void
; - delete! var     -> void
; - extended        -> env
; - to-string       -> string
;

; choose implementation here
(load "environment1.scm")
(define environment environment1)





