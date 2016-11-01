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
  (display "check1: exp = ")(display exp)(newline)
  (let ((operator (exp-operator exp))
        (operands (exp-operands exp)))
    (let ((proc (lazy-eval operator env))
          (args (map (lambda (x) (lazy-eval x env)) operands)))
      (display "check2: proc = ")(display proc)(newline)
      (display "check3: (force-thunk proc) = ")(display (force-thunk proc))(newline)
      (display "check4: args = ")(display args)(newline)
      (display "check5: (map force-thunk args) = ")
        (display (map force-thunk args))(newline)
      (lazy-apply proc args))))

))  ; include guard
