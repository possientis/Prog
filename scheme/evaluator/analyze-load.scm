;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-load)) 
  (begin
    (define included-analyze-load #f)  ; include guard
    (display "loading analyze-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (analyze-load filename)
  (let ((code (filename->code filename)))
    (analyze-eval code)
    unspecified-value))

))  ; include guard
