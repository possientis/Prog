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
        ((primitive-procedure? exp) #t)
        ((eval-procedure? exp) #t)
        ((analyze-procedure? exp))
        (else #f)))

; strict eval
(define (strict-eval-self-evaluating exp env) exp)

; analyze
(define (analyze-self-evaluating exp) (lambda (env) exp)) 

; lazy eval  
; creates an 'evaluated' thunk which has no embedded environment
(define (lazy-eval-self-evaluating exp env) (thunk exp '()))


))  ; include guard
