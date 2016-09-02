;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-defined)) 
  (begin
    (define included-defined #f)
    (display "loading defined")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; we are following what appears to be the scm semantics in the case when the
; expression does not refer to a variable. Instead of throwing an error, we
; simply return #f.

; testing
(define (is-defined? exp) (tagged-list? exp 'defined?))

; destructuring
(define (defined?-variable exp) (cadr exp))

; eval
(define (eval-defined? exp env)
  (let ((var (defined?-variable exp))) 
    (if (not (variable? var)) #f  ((env 'defined?) var)))) 

; analyze
(define (analyze-defined? exp)
  (let ((var (defined?-variable exp)))
    (if (not (variable? var)) ; test is done at 'analyze' time, not runtime
      (lambda (env) #f)
      (lambda (env) ((env 'defined?) var))))) 

; lazy
(define (lazy-eval-defined? exp env) (thunk exp env))

))  ; include guard

    





