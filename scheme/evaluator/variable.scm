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
(define strict-map-primitive (make-primitive-procedure strict-map))

(define analyze-apply-primitive (make-primitive-procedure analyze-apply))
(define analyze-eval-primitive (make-primitive-procedure analyze-eval))
(define analyze-load-primitive (make-primitive-procedure analyze-load))
(define analyze-map-primitive (make-primitive-procedure analyze-map))

(define lazy-apply-primitive (make-primitive-procedure lazy-apply))
(define lazy-eval-primitive (make-primitive-procedure lazy-eval))
(define lazy-load-primitive (make-primitive-procedure lazy-load))
(define lazy-map-primitive (make-primitive-procedure lazy-map))

; strict eval
(define (strict-eval-variable exp env)
  (cond ((equal? exp 'apply) strict-apply-primitive)
        ((equal? exp 'eval) strict-eval-primitive)
        ((equal? exp 'load) strict-load-primitive)
        ((equal? exp 'map) strict-map-primitive)
        (else (let ((value ((env 'lookup) exp)))
                value))))
;                (force-thunk value))))) 

; analyze
(define (analyze-variable exp) 
  (cond ((equal? exp 'apply) (lambda (env) analyze-apply-primitive))
        ((equal? exp 'eval) (lambda (env) analyze-eval-primitive))
        ((equal? exp 'load) (lambda (env) analyze-load-primitive))
        ((equal? exp 'map) (lambda (env) analyze-map-primitive))
        (else (lambda (env) (let ((value ((env 'lookup) exp))) 
                              value)))))
;                              (force-thunk value))))))

; lazy eval
(define (lazy-eval-variable exp env)
  (debug "[DEBUG]: lazy-eval-variable: exp = ")(debug exp)(debug-newline)
  (cond ((equal? exp 'apply) lazy-apply-primitive)
        ((equal? exp 'eval) lazy-eval-primitive)
        ((equal? exp 'load) lazy-load-primitive)
        ((equal? exp 'map) lazy-map-primitive)
        (else (let ((value ((env 'lookup) exp)))
                (debug "[DEBUG]: lazy-eval-variable: value = ")
                (debug value)(debug-newline)
                (if (thunk? value)
                  (begin
                    (debug "[DEBUG]: lazy-eval-variable: value is a thunk")
                    (debug-newline)
                    (if (thunk-evaluated? value)
                      (begin
                        (debug "[DEBUG]: lazy-eval-variable: value is evaluated")
                        (debug-newline)
                        (debug "[DEBUG]: lazy-eval-variable: forced-value = ")
                        (debug ((cadr value) 'value)) (debug-newline)
                        (debug "[DEBUG]: lazy-eval-variable: env = ")
                        (debug (thunk-environment value))(debug-newline))))
                  (begin
                    (debug "[DEBUG]: lazy-eval-variable: value is not a thunk")
                    (debug-newline)))
                (if (thunk? value) value
                  (make-thunk value '())))))) ; evaluated thunk from value

))  ; include guard
