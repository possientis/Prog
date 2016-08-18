;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-load)) 
  (begin
    (define included-new-load #f)  ; include guard
    (display "loading new-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (new-load filename)
  (let ((code (filename->code filename)))
    (new-eval code)
    (string-append " " filename " loaded")))

))  ; include guard
