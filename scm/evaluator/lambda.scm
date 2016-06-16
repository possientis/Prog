;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lambda)) 
  (begin
    (define included-lambda #f)
    (display "loading lambda")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "begin.scm")

; Note: a lambda expression is valid scheme code. 

; When evaluating a lambda expression, we return some object 
; (an 'eval-procedure') which is no longer scheme code, but is 
; a valid argument to the function 'apply-eval-procedure'.

; When analyzing a lambda expression, we return an object
; (an 'analyze-procedure') which is no longer scheme code, but is
; a valid argument to the function 'apply-analyze-procedure'.


; testing
(define (lambda? exp) (tagged-list? exp 'lambda))

; making
(define (make-lambda parameters body) (cons 'lambda (cons parameters body)))

; destructuring
(define (lambda-params exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

; eval
(define (eval-lambda exp env)
  (let ((params (lambda-params exp))
        (body (lambda-body exp)))
    (let ((eval-body (make-begin body)))
      (make-eval-procedure params eval-body env))))

; analyze
(define (analyze-lambda exp)
  (let ((params (lambda-params exp))
        (body (lambda-body exp)))
    (let ((analyze-body (analyze-sequence body)))
      (lambda (env)
        (make-analyze-procedure params analyze-body env)))))

))  ; include guard

