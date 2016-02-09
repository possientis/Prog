(load "frame1")
; required interface for frame
;
; - insert! var val -> void
; - delete! var     -> void
; - find    var     -> (var,val) or #f
;
(define frame frame1)
