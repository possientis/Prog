;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-load)) 
  (begin
    (define included-strict-load #f)  ; include guard
    (display "loading strict-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (strict-load filename . arg)
  (let ((env (if (null? arg) global-env (car arg))) 
        (code (filename->code filename)))
    (strict-eval code env)
    unspecified-value))

))  ; include guard
