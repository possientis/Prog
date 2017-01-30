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
  (let ((pred (strict-eval (not-predicate exp) env)))
    (if (true? pred) #f #t)))  

; analyze
(define (analyze-not exp)
  (let ((pred (analyze (not-predicate exp))))
    (lambda (env)
      (if (true? (pred env)) #f #t))))

; lazy eval
(define (lazy-eval-not exp env) 
  (debug "[DEBUG]: lazy-eval-not: exp = ")(debug exp)(debug-newline)
  (make-thunk exp env))

))  ; include guard


