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
(load "environment1")
(define environment environment1)
(load "primitive.scm")

(define (setup-environment)
  (let ((initial-env
          (((environment) 'extended)
           (primitive-procedure-names)
           (primitive-procedure-objects))))
    ((initial-env 'define!) 'true #t)
    ((initial-env 'define!) 'false #f)
    initial-env))

(define global-env (setup-environment))

;(display (global-env 'to-string))(newline)





