; required interface for frame
;
; - empty?  void    -> bool
; - insert! var val -> void
; - delete! var     -> void
; - find    var     -> (var,val) or #f
;

; choose implementation here
(load "frame2")
(define frame frame2)
