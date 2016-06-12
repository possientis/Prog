;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-let-rec)) 
  (begin
    (define included-let-rec #f)
    (display "loading let-rec")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "lambda.scm")

; testing
(define (letrec? exp) (tagged-list? exp 'letrec))

; destructuring
(define (letrec-bindings exp) (cadr exp))
(define (letrec-body exp) (cddr exp))

(define (letrec-binding->define binding)
  (list 'define (car binding) (cadr binding)))

(define (letrec-define-list exp)
  (map letrec-binding->define (letrec-bindings exp)))

(define (letrec-new-body exp)
  (append (letrec-define-list exp) (letrec-body exp)))

(define (letrec->combination exp)
  (list (make-lambda '() (letrec-new-body exp))))

))  ; include guard
