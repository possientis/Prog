;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-if)) 
  (begin
    (define included-if #f)
    (display "loading if")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (if? exp) (tagged-list? exp 'if))

; making
(define (make-if predicate consequent alternative) 
  (list 'if predicate consequent alternative))

; destructuring
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp) 
  (if (not (null? (cdddr exp))) (cadddr exp) #f))

; strict eval
(define (strict-eval-if exp env)
  (let ((pred (strict-eval (if-predicate exp) env)))
    (if pred
      (strict-eval (if-consequent exp) env)
      (strict-eval (if-alternative exp) env))))

; analyze
(define (analyze-if exp)
  (let ((pred   (analyze (if-predicate exp)))
        (conseq (analyze (if-consequent exp)))
        (alter  (analyze (if-alternative exp))))
    (lambda (env)
      (if (pred env) (conseq env) (alter env)))))

; predicate is strictly evaluated, so branching can occur

; lazy eval
(define (lazy-eval-if exp env) 
  (let ((pred (force-thunk (lazy-eval (if-predicate exp) env))))
    (if pred
      (lazy-eval (if-consequent exp) env)
      (lazy-eval (if-alternative exp) env))))

; note: memoization is likely to be a problem here



))  ; include guard
