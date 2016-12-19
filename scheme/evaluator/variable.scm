;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-variable)) 
  (begin
    (define included-variable #f)
    (display "loading variable")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "primitive.scm")
(load "primitive-procedure.scm")

; testing
(define (variable? exp) (symbol? exp))

; helper
(define strict-apply-primitive (make-primitive-procedure strict-apply))
(define strict-eval-primitive (make-primitive-procedure strict-eval))
(define analyze-apply-primitive (make-primitive-procedure analyze-apply))
(define analyze-eval-primitive (make-primitive-procedure analyze-eval))
(define lazy-apply-primitive (make-primitive-procedure lazy-apply))
(define lazy-eval-primitive (make-primitive-procedure lazy-eval))

; strict eval
(define (strict-eval-variable exp env)
  (cond ((equal? exp 'apply) strict-apply-primitive)
        ((equal? exp 'eval) strict-eval-primitive)
        (else (let ((value ((env 'lookup) exp)))
                (force-thunk value)))))

; analyze
(define (analyze-variable exp) 
  (cond ((equal? exp 'apply) (lambda (env) analyze-apply-primitive))
        ((equal? exp 'eval) (lambda (env) analyze-eval-primitive))
        (else (lambda (env) (let ((value ((env 'lookup) exp))) 
                              (force-thunk value))))))

; lazy eval
(define (lazy-eval-variable exp env)
  (debug "lazy-eval-variable: exp = ")(debug exp)(debug-newline)
  (cond ((equal? exp 'apply) lazy-apply-primitive)
        ((equal? exp 'eval) lazy-eval-primitive)
        (else (let ((value ((env 'lookup) exp)))
                (debug "lazy-eval-variable: value = ")(debug value)(debug-newline)
                (if (thunk? value) value
                  (make-thunk value '())))))) ; evaluated thunk from value

))  ; include guard
