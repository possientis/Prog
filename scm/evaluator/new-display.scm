;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-display)) 
  (begin
    (define included-new-display #f)
    (display "loading new-display")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; adding a visible mark distinguishing the interpreter's
; output from that of native scheme.
(define (new-display object)
  (display "***")(display object))

))  ; include guard
