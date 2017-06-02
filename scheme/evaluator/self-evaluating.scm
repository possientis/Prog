;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-self-evaluating)) 
  (begin
    (define included-self-evaluating #f)
    (display "loading self-evaluating")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

; testing
(define (self-evaluating? exp) 
  (cond ((number? exp) #t)
        ((string? exp) #t)
        ((char? exp)  #t)
        ((boolean? exp) #t)
        ((vector? exp) #t)
        (else #f)))

; strict eval
(define (strict-eval-self-evaluating exp env) exp)

; analyze
(define (analyze-self-evaluating exp) (lambda (env) exp)) 

; lazy eval  
; function returns value rather than evaluated thunk encapsulating value.
; for some reason, this abuse of the type system works fine.
(define (lazy-eval-self-evaluating exp env) 
  exp)


))  ; include guard
