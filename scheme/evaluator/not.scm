;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-not)) 
  (begin
    (define included-not #f)
    (display "loading not")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (not? exp) (tagged-list? exp 'not))

; making
(define (make-not predicate) (list 'not predicate))

; destructuring
(define (not-predicate exp) (cadr exp))

; strict eval
(define (strict-eval-not exp env)
  (not (strict-eval (not-predicate exp) env)))

; analyze
(define (analyze-not exp)
  (let ((pred (analyze (not-predicate exp))))
    (lambda (env)
      (not (pred env)))))

; lazy eval
(define (lazy-eval-not exp env) 
  (make-thunk exp env))

))  ; include guard


