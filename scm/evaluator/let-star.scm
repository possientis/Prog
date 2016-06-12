;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-let-star)) 
  (begin
    (define included-let-star #f)
    (display "loading let-star")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "let.scm")

; testing
(define (let*? exp) (tagged-list? exp 'let*))

; destructuring
(define (let*-bindings exp) (cadr exp))
(define (let*-body exp) (cddr exp))

(define (single-binding? binding) (null? (cdr binding)))

(define (let*->nested-lets exp)
  (let ((bindings (let*-bindings exp)))
    (let-expand bindings (let*-body exp))))

(define (let-expand bindings body)
  (if (single-binding? bindings)
    (make-let bindings body)
    (make-let (list (car bindings))
              (list (let-expand (cdr bindings) body)))))

))  ; include guard
