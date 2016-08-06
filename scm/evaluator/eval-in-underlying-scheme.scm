;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-eval-in-underlying-scheme)) 
  (begin
    (define included-eval-in-underlying-scheme #f)
    (display "loading eval-in-underlying-scheme")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; safeguarding the primitive procedure 'apply' before redefining it
(define eval-in-underlying-scheme eval)

))  ; include guard
