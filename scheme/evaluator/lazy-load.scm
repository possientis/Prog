;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-load)) 
  (begin
    (define included-lazy-load #f)  ; include guard
    (display "loading lazy-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (lazy-load filename . arg)
  (let ((env (if (null? arg) global-env (car arg))) 
        (code (filename->code filename)))
    (lazy-eval code env)
    unspecified-value))

))  ; include guard
