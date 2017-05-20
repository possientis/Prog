(require 'macro)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-define-syntax)) 
  (begin
    (define included-define-syntax #f)
    (display "loading define-syntax")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (define-syntax? exp) (tagged-list? exp 'define-syntax))

; destructuring
(define (define-syntax-expr exp) (cdr exp))

; strict-eval
(define (strict-eval-define-syntax exp env)
  'ok)  ; ignore

; analyze
(define (analyze-define-syntax exp)
  (lambda (env) 'ok))


; lazy eval
(define (lazy-eval-define-syntax exp env)
  'ok)

))  ; include guard.
