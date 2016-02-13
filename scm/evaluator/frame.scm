; required interface for frame
;
; - insert! var val -> void
; - delete! var     -> void
; - find    var     -> (var,val) or #f
;

; choose implementation here
(load "frame1")
(define frame frame1)
