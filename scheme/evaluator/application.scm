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

; strict eval
(define (strict-eval-application exp env)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (strict-eval operator env))
          (args (map (lambda (x) (strict-eval x env)) operands)))
      (strict-apply proc args))))

; analyze
(define (analyze-application exp)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (analyze operator))
          (args (map analyze operands)))
      (lambda (env)
        (analyze-apply (proc env) (map (lambda (x) (x env)) args))))))

; lazy
(define (lazy-eval-application exp env)
  (debug "[DEBUG]: ***************** Start *********************\n")
  (debug "[DEBUG]: lazy-eval-application: exp = ")(debug exp)(debug-newline)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (strict-eval operator env))
          (args (map (lambda (x) (lazy-eval x env)) operands)))

      (debug "[DEBUG]: lazy-eval-application: proc = ")(debug proc)(debug-newline)
      (debug "[DEBUG]: lazy-eval-application: args = ")(debug args)(debug-newline)
      (debug "[DEBUG]: ****************** End **********************\n")
      (lazy-apply proc args))))


))  ; include guard
