;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lambda)) 
  (begin
    (define included-lambda #f)
    (display "loading lambda")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; Note: a lambda expression is valid scheme code. 

; When evaluating a lambda expression, we return some object 
; (an 'eval-procedure') which is no longer scheme code, but is 
; a valid argument to the function 'apply-eval-procedure'.

; When analyzing a lambda expression, we return a map taking an environment
; as input and returning an object (an 'analyze-procedure') which is no longer
; scheme code, but is a valid argument to the function 'apply-analyze-procedure'.

; Evaluating a lambda expression does not do much: It simply, unpacks the data
; contained within the lambda expression (params and body) and repackages it 
; in a new wrapper inside which an environment object is also included. As
; an implementation detail, the body of the lambda expression is converted
; from a list of expressions to a single 'begin' expression, thereby removing
; the direct dependency of apply-eval-procedure to code relating to sequence 
; evaluation.

; Analyzing a lambda expression is similar in structure to the evaluation. One
; key difference however is that the 'begin' expression which constitutes the
; body of the corresponding eval-procedure is analyzed in the analyze-procedure.

; testing
(define (lambda? exp) (tagged-list? exp 'lambda))

; making
(define (make-lambda parameters body) (cons 'lambda (cons parameters body)))

; destructuring
(define (lambda-params exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

; strict eval
(define (strict-eval-lambda exp env)
  (let ((params (lambda-params exp))
        (body (lambda-body exp)))
    (let ((eval-body (make-begin body)))
      (make-eval-procedure params eval-body env))))

; analyze
(define (analyze-lambda exp)
  (let ((params (lambda-params exp))
        (body (lambda-body exp)))
    (let ((analyze-body (analyze (make-begin body))))
      (lambda (env)
        (make-analyze-procedure params analyze-body env)))))

; lazy eval
(define (lazy-eval-lambda exp env)
  (let ((params (lambda-params exp))
        (body (lambda-body exp)))
    (let ((eval-body (make-begin body)))
      (make-eval-procedure params eval-body env))))



))  ; include guard

