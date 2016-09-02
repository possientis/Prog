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

; eval
(define (eval-if exp env)
  (let ((pred (new-eval (if-predicate exp) env)))
    (if (true? pred)
      (new-eval (if-consequent exp) env)
      (new-eval (if-alternative exp) env))))

; analyze
(define (analyze-if exp)
  (let ((pred   (analyze (if-predicate exp)))
        (conseq (analyze (if-consequent exp)))
        (alter  (analyze (if-alternative exp))))
    (lambda (env)
      (if (true? (pred env)) (conseq env) (alter env)))))

; lazy
(define (lazy-eval-if exp env) 
  (let ((pred ((lazy-eval (if-predicate exp) env) 'value)))
    (if (true? pred)
      (lazy-eval (if-consequent exp) env)
      (lazy-eval (if-alternative exp) env))))

; note: memoization is likely to be a problem here



))  ; include guard
