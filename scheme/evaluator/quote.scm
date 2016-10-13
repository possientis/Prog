;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-quote)) 
  (begin
    (define included-quote #f)
    (display "loading quote")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (quoted? exp) (tagged-list? exp 'quote))                                    

; destructuring
(define (text-of-quotation exp) (cadr exp))

; strict eval
(define (strict-eval-quoted exp env) (text-of-quotation exp))

; analyze
(define (analyze-quoted exp)
  (let ((qval (text-of-quotation exp)))
    (lambda (env) qval)))

; lazy eval
(define (lazy-eval-quoted exp env) (make-thunk exp 'dummy-env))

))  ; include guard
