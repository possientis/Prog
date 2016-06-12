;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lambda)) 
  (begin
    (define included-lambda #f)
    (display "loading lambda")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "operands.scm")

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
    (make-eval-procedure params body env)))

; analyze
(define (analyze-lambda exp)
  (let ((params (lambda-params exp))
        (body (lambda-body exp)))
    (let ((bproc (analyze-sequence body)))
      (lambda (env)
        (make-analyze-procedure params bproc env)))))

))  ; include guard

