;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-let)) 
  (begin
    (define included-let #f)
    (display "loading let")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (let? exp) (and (tagged-list? exp 'let) (not (symbol? (cadr exp))))) 

; making
(define (make-let bindings body) (cons 'let (cons bindings body)))

; destructuring
(define (let-bindings exp) (cadr exp))
(define (let-body exp) (cddr exp))
(define (let-parameters exp) (map car (let-bindings exp)))
(define (let-operands exp) (map cadr (let-bindings exp)))

; strict eval
(define (strict-eval-let exp env)
  (strict-eval (let->combination exp) env))

; analyze
(define (analyze-let exp)
  (analyze (let->combination exp)))

; lazy eval
(define (lazy-eval-let exp env)
  (lazy-eval (let->combination exp) env))


(define (let->combination exp)
  (cons (make-lambda (let-parameters exp) (let-body exp)) (let-operands exp)))

))  ; include guard

