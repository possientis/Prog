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
      (force-thunk args)              ; for strict evaluation within lazy scheme 
      (strict-apply proc args))))

; analyze
(define (analyze-application exp)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (analyze operator))
          (args (map analyze operands)))
      (lambda (env)
        (let ((forced-args (map (lambda (x) (x env)) args)))
          (force-thunk forced-args)   ; for analyze evaluation within lazy scheme
          (analyze-apply (proc env) forced-args))))))

; lazy
(define (lazy-eval-application exp env)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (force-thunk (lazy-eval operator env)))
          (args (map (lambda (x) (make-thunk x env)) operands))) 
      (lazy-apply proc args))))


))  ; include guard
