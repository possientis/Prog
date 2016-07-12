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

; eval
(define (eval-let exp env)
  (eval (let->combination exp) env))

; analyze
(define (analyze-let exp)
  (analyze (let->combination exp)))


(define (let->combination exp)
  (cons (make-lambda (let-parameters exp) (let-body exp)) (let-operands exp)))

))  ; include guard

