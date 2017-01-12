;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-load)) 
  (begin
    (define included-analyze-load #f)  ; include guard
    (display "loading analyze-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (analyze-load filename)
  (let ((env global-env) (code (filename->code filename)))
    (analyze-eval code env)
    unspecified-value))

))  ; include guard
