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
      ((env 'define!) var val))))

; analyze
(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (rhs (definition-expression exp)))
    (let ((val (analyze rhs)))
      (lambda (env) ((env 'define!) var (val env)))))) 

; lazy eval
(define (lazy-eval-definition exp env) (thunk exp env)) 

))  ; include guard

