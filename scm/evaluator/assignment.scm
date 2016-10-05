;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-assignment)) 
  (begin
    (define included-assignment #f)
    (display "loading assignment")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (assignment? exp) (tagged-list? exp 'set!))

; destructuring
(define (assignment-variable exp) (cadr exp))
(define (assignment-expression exp) (caddr exp))

; strict eval
(define (strict-eval-assignment exp env)
  (let ((var (assignment-variable exp))
        (rhs (assignment-expression exp)))
    (let ((val (strict-eval rhs env)))
      ((env 'set!) var val)
      unspecified-value)))

; analyze
(define (analyze-assignment exp)
  (let ((var (assignment-variable exp))
        (rhs (assignment-expression exp)))
    (let ((val (analyze rhs)))
      (lambda (env) ((env 'set!) var (val env))))))

; lazy eval
(define (lazy-eval-assignment exp env)
  (let ((var (assignment-variable exp))
        (rhs (assignment-expression exp)))
    (let ((val (lazy-eval rhs env)))
      ((env 'set!) var val)
      (thunk unspecified-value '()))))  ; should always return a thunk

; REVISE COMMENT
; note: the side-effect actually occurs when the thunk is forced
; because our implementation uses memoization in the forcing of
; thunks, repeated forcing only creates the side effect once.
; This can lead to surprising semantics. 

))  ; include guard
