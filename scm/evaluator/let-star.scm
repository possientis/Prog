;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-let-star)) 
  (begin
    (define included-let-star #f)
    (display "loading let-star")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (let*? exp) (tagged-list? exp 'let*))

(define (single-binding? binding) (null? (cdr binding)))

; destructuring
(define (let*-bindings exp) (cadr exp))
(define (let*-body exp) (cddr exp))

; eval
(define (eval-let* exp env)
  (eval (let*->nested-lets exp) env))

; analyze
(define (analyze-let* exp)
  (analyze (let*->nested-lets exp)))

(define (let*->nested-lets exp)
  (let ((bindings (let*-bindings exp)))
    (let-expand bindings (let*-body exp))))

(define (let-expand bindings body)
  (if (single-binding? bindings)
    (make-let bindings body)
    (make-let (list (car bindings))
              (list (let-expand (cdr bindings) body)))))

))  ; include guard
