;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-quote)) 
  (begin
    (define included-quote #f)
    (display "loading quote")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")

; testing
(define (quoted? exp) (tagged-list? exp 'quote))                                    

; destructuring
(define (text-of-quotation exp) (cadr exp))

; eval
(define (eval-quoted exp env) (text-of-quotation exp))

; analyze
(define (analyze-quoted exp)
  (let ((qval (text-of-quotation exp)))
    (lambda (env) qval)))

))  ; include guard
