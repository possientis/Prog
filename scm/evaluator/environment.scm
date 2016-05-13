;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-environment)) 
  (begin
    (define included-environment #f)
    (display "loading environment")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


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


))  ; include guard


