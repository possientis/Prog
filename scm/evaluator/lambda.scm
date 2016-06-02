;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lambda)) 
  (begin
    (define included-lambda #f)
    (display "loading lambda")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "make.scm")
(load "operands.scm")

; destructuring
(define (lambda-params exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

; eval
(define (eval-lambda exp env)
  (let ((params (lambda-params exp))
        (body (lambda-body exp)))
    (make-procedure params body env)))

; analyze
(define (analyze-lambda exp)
;(display "lambda1: exp = ")(display exp)(newline)
;(display "lambda2: vars = ")(display (lambda-params exp))(newline)
;(display "lambda3: body =")(display (lambda-body exp))(newline)
;(display "lambda4: analyzed-body = ")(display(analyze-sequence (lambda-body exp)))
;(newline)
  (let ((vars (lambda-params exp))
        (bproc (analyze-sequence (lambda-body exp))))
    (lambda (env)
      (make-procedure vars bproc env))))

))  ; include guard

