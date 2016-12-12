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
  (cond ((equal? exp 'apply) (make-primitive-procedure strict-apply))
        ((equal? exp 'eval) (make-primitive-procedure strict-eval))
        (else (let ((value ((env 'lookup) exp)))
                value)))) ; forcing value here creates failure, why?

; analyze
(define (analyze-variable exp) 
  (lambda (env)
    (let ((value ((env 'lookup) exp)))
      value)))  ; do not force when value is a thunk

; lazy eval
(define (lazy-eval-variable exp env)
  (debug "lazy-eval-variable: exp = ")(debug exp)(debug-newline)
  (let ((value ((env 'lookup) exp)))
    (debug "lazy-eval-variable: value = ")(debug value)(debug-newline)
    (if (thunk? value)
      value
      (make-thunk value '())))) ; creating evaluated thunk from value

))  ; include guard
