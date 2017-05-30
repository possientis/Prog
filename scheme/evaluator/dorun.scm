(require 'macro)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-dorun)) 
  (begin
    (define included-dorun #f)
    (display "loading dorun")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; only used by native scheme
(define-syntax dorun
  (syntax-rules ()
    ((dorun expr ...)
     (begin expr ...))))

; testing
(define (dorun? exp) (tagged-list? exp 'dorun))

; destructuring
(define (dorun-expr exp) 
  (cons 'begin (cdr exp)))

; strict-eval
(define (strict-eval-dorun exp env)
  (strict-eval (dorun-expr exp) env))

; analyze
(define (analyze-dorun exp)
  (analyze (dorun-expr exp)))

; lazy eval
(define (lazy-eval-dorun exp env)
  (strict-eval (dorun-expr exp) env))

))  ; include guard.
