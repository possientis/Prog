;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-definition)) 
  (begin
    (define included-definition #f)
    (display "loading definition")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; definition semantics differ from that of assignment. One important difference is
; the syntactic construct (define (f args) body) which has no assignment equivalent

; testing
(define (definition? exp) (tagged-list? exp 'define))

; destructuring
(define (definition-variable exp)
  (if (symbol? (cadr exp)) (cadr exp) (caadr exp)))

(define (definition-expression exp)
  (if (symbol? (cadr exp))
    (caddr exp)
    (make-lambda (cdadr exp)                                   
                 (cddr exp))))

; strict eval
(define (strict-eval-definition exp env)
  (let ((var (definition-variable exp))
        (rhs (definition-expression exp)))
    (let ((val (strict-eval rhs env)))
      ((env 'define!) var val)
      unspecified-value)))

; analyze
(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (rhs (definition-expression exp)))
    (let ((val (analyze rhs)))
      (lambda (env) ((env 'define!) var (val env))
        unspecified-value))))

; lazy eval
(define (lazy-eval-definition exp env)
  (let ((var (definition-variable exp))
        (rhs (definition-expression exp)))
    (let ((val (lazy-eval rhs env)))
      ((env 'define!) var val)                ; val is a thunk
      (make-thunk unspecified-value '()))))   ; should always return a thunk

; Note: the side effect resulting from a lazy definition takes place immediately.
; In other words, the creation of a new binding is not delayed. However, the 
; definition expression is not evaluated. Instead, a thunk is created and the 
; variable is bound to this thunk.


))  ; include guard


