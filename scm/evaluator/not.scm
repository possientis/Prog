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

; eval
(define (eval-not exp env)
  (let ((pred (eval (not-predicate exp) env)))
    (if (true? pred) #f #t)))  

; analyze
(define (analyze-not exp)
  (let ((pred (analyze (not-predicate exp))))
    (lambda (env)
      (if (true? (pred env)) #f #t))))

))  ; include guard


