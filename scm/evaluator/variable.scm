;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-variable)) 
  (begin
    (define included-variable #f)
    (display "loading variable")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (variable? exp) (symbol? exp))

; eval
(define (eval-variable exp env) ((env 'lookup) exp))

; analyze
(define (analyze-variable exp) (lambda (env) ((env 'lookup) exp)))

; lazy
(define (lazy-eval-variable exp env)
  (let ((possible-thunk ((env 'lookup) exp)))
    (if (thunk? possible-thunk)
      possible-thunk
      (thunk possible-thunk '())))) ; creating evaluated thunk from value

))  ; include guard
