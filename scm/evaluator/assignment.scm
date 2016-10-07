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
      (lambda (env) ((env 'set!) var (val env))
       unspecified-value ))))

; lazy eval
(define (lazy-eval-assignment exp env)
  (let ((var (assignment-variable exp))
        (rhs (assignment-expression exp)))
    (let ((val (lazy-eval rhs env)))
      ((env 'set!) var val)             ; val is a thunk
      (thunk unspecified-value '()))))  ; should always return a thunk

; Note: the side effect resulting from a lazy assignment takes place immediately.
; In other words, the change in binding is not delayed. However, the assignment
; expression is not evaluated. Instead, a thunk is created and the variable is
; bound to this thunk.

))  ; include guard
