;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-load)) 
  (begin
    (define included-strict-load #f)  ; include guard
    (display "loading strict-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (strict-load filename)
  (let ((code (filename->code filename)))
    (strict-eval code)
    unspecified-value))

))  ; include guard
