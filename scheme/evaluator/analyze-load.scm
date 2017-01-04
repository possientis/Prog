;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-load)) 
  (begin
    (define included-analyze-load #f)  ; include guard
    (display "loading analyze-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (analyze-load filename . arg)
  (let ((env (if (null? arg) global-env (car arg))) 
        (code (filename->code filename)))
    (analyze-eval code env)
    unspecified-value))

))  ; include guard
