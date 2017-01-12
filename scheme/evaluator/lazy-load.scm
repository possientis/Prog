;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-load)) 
  (begin
    (define included-lazy-load #f)  ; include guard
    (display "loading lazy-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (lazy-load filename)
  (let ((env global-env) (code (filename->code filename)))
    (lazy-eval code env)
    unspecified-value))

))  ; include guard
