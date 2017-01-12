;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-load)) 
  (begin
    (define included-strict-load #f)  ; include guard
    (display "loading strict-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The strict-load function is fundamentally a strict-eval function.
; The only difference lies in the argument referring to the expression
; being evaluated. In the case of strict-load, the expression being 
; evaluated is simply the code contained within the filename argument.
;
; However, contrary to strict-eval which has an optional environment 
; argument, we have chosen not to include such argument for strict-load
;
;  
(define (strict-load filename)
  (let ((env global-env) (code (filename->code filename)))
    (strict-eval code env)
    unspecified-value))

))  ; include guard
