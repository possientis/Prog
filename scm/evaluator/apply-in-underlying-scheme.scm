;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-apply-in-underlying-scheme)) 
  (begin
    (define included-apply-in-underlying-scheme #f)
    (display "loading apply-in-underlying-scheme")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; safeguarding the primitive procedure 'apply' before redefining it
(define apply-in-underlying-scheme apply)

))  ; include guard
