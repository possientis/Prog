;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-variable)) 
  (begin
    (define included-variable #f)
    (display "loading variable")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (variable? exp) (symbol? exp))

; strict eval
(define (strict-eval-variable exp env)
  (let ((value ((env 'lookup) exp)))
    value))

; analyze
(define (analyze-variable exp) 
  (lambda (env)
    (let ((value ((env 'lookup) exp)))
      value)))

; lazy eval
(define (lazy-eval-variable exp env)
  (let ((value ((env 'lookup) exp)))
    (if (thunk? value)
      value
      (make-thunk value '())))) ; creating evaluated thunk from value

))  ; include guard
