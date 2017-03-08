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

; strict eval
(define (strict-eval-defined? exp env)
  (let ((var (defined?-variable exp))) 
    (if (not (variable? var)) #f  ((env 'defined?) var)))) 

; analyze
(define (analyze-defined? exp)
  (let ((var (defined?-variable exp)))
    (if (not (variable? var)) ; test is done at 'analyze' time, not runtime
      (lambda (env) #f)
      (lambda (env) ((env 'defined?) var))))) 

; It feels like the evaluation should not be delayed: when testing whether
; a binding exists for a variable, we probably want to know the answer for
; the current state of the environment, not the (future) state when the 
; thunk is actually being evaluated. However, it is likely that this decision 
; has no impact, as an 'if' statement will probably force the thunk before 
; branching anyway.

; lazy eval
(define (lazy-eval-defined? exp env)
  (strict-eval-defined? exp env))

))  ; include guard

    





