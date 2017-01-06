;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-frame)) 
  (begin
    (define included-frame #f)
    (display "loading frame")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; required interface for frame
;
; - empty?  void    -> bool
; - insert! var val -> void
; - delete! var     -> void
; - find    var     -> (var,val) or #f
;

; choose implementation here
(load "frame3.scm")
(define frame frame3)

))  ; include guard
