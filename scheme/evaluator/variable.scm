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
    (if (thunk? value)
;      (force-thunk value) ; <------- key change, induces failure via run
      value
      value)))

; analyze
(define (analyze-variable exp) 
  (lambda (env)
    (let ((value ((env 'lookup) exp)))
      (if (thunk? value)
;        (force-thunk value)
        value
        value))))

; lazy eval
(define (lazy-eval-variable exp env)
  (let ((value ((env 'lookup) exp)))
    (if (thunk? value)
      value
      (thunk value '())))) ; creating evaluated thunk from value

))  ; include guard
