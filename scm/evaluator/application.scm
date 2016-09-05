;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-application)) 
  (begin
    (define included-application #f)
    (display "loading application")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (application? exp) (pair? exp)) ; need to be tested last

; destructuring
(define (exp-operator exp) (car exp))
(define (exp-operands exp) (cdr exp))

; eval
(define (eval-application exp env)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (new-eval operator env))
          (args (map (lambda (x) (new-eval x env)) operands)))
      (new-apply proc args))))

; analyze
(define (analyze-application exp)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (analyze operator))
          (args (map analyze operands)))
      (lambda (env)
        (new-apply (proc env) (map (lambda (x) (x env)) args))))))

; lazy
(define (lazy-eval-application exp env)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (lazy-eval operator env))
          (args (map (lambda (x) (lazy-eval x env)) operands)))
      (lazy-apply proc args))))

))  ; include guard
