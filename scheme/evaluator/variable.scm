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
(define strict-load-primitive (make-primitive-procedure strict-load))

(define analyze-apply-primitive (make-primitive-procedure analyze-apply))
(define analyze-eval-primitive (make-primitive-procedure analyze-eval))
(define analyze-load-primitive (make-primitive-procedure analyze-load))

(define lazy-apply-primitive (make-primitive-procedure lazy-apply))
(define lazy-eval-primitive (make-primitive-procedure lazy-eval))
(define lazy-load-primitive (make-primitive-procedure lazy-load))

; strict eval
(define (strict-eval-variable exp env)
  (cond ((equal? exp 'apply) strict-apply-primitive)
        ((equal? exp 'eval) strict-eval-primitive)
        ((equal? exp 'load) strict-load-primitive)
        (else (let ((value ((env 'lookup) exp)))
                value))))
;                (force-thunk value))))) 

; analyze
(define (analyze-variable exp) 
  (cond ((equal? exp 'apply) (lambda (env) analyze-apply-primitive))
        ((equal? exp 'eval) (lambda (env) analyze-eval-primitive))
        ((equal? exp 'load) (lambda (env) analyze-load-primitive))
        (else (lambda (env) (let ((value ((env 'lookup) exp))) 
                              value)))))
;                              (force-thunk value))))))

; lazy eval
(define (lazy-eval-variable exp env)
  (cond ((equal? exp 'apply) lazy-apply-primitive)
        ((equal? exp 'eval) lazy-eval-primitive)
        ((equal? exp 'load) lazy-load-primitive)
        (else (let ((value ((env 'lookup) exp)))
                (if (thunk? value) value
                  (make-thunk value '())))))) ; evaluated thunk from value

))  ; include guard
