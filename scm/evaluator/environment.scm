; required interface for environment
;
; - lookup-variable-value var env     -> val
; - set-variable-value! var val env   -> void
; - define-variable! var val env      -> void
; - extend-environment vars vals env  -> env
; - display-environment               -> env
;

(define (environment) (environment1)) ; choose implementation here

(define environment1    ; constructor
  (let ((_static #f))   ; name encapsulation
    ; object built from data is message passing interface
    (define (this data) ; data ignored here
      (lambda(m)
        (cond ((eq? m 'lookup-variable-value)(lookup-variable-value data))
              ((eq? m 'set-variable-value!)(set-variable-value! data))
              ((eq? m 'define-variable!)(define-variable-value! data))
              ((eq? m 'extend-environment)(extend-environment data))
              ((eq? m 'display-environment)(display-environment data))
              (else (error "environment1: unknown operation error: " m)))))
    ;
    (define (lookup-variable-value data)
      'TBI)
    ;
    (define (set-variable-value! data)
      'TBI)
    ;
    (define (define-variable-value! data)
      'TBI)
    ;
    (define (extend-environment data)
      'TBI)
    ;
    (define (display-environment data)
      (display data)(newline))
    ; returning no argument constructor
    (lambda () (this (list (cons '() '()))))))
    


(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment (list (cons '() '())))
(define (make-frame variables values) (cons variables values))
(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
    (cons (make-frame vars vals) base-env)
    (if (< (length vars) (length vals))
      (error "Too many arguments supplied" vars vals)
      (error "Too few arguments supplied" vars vals))))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars) (env-loop (enclosing-environment env)))
            ((eq? var (car vars)) (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
      (error "Unbound variable" var)
      (let ((frame (first-frame env)))
        (scan (frame-variables frame) (frame-values frame)))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars val)
      (cond ((null? vars) (env-loop (enclosing-environment env)))
            ((eq? var (car vars)) (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
      (error "Unbound variable -- SET!" var)
      (let ((frame (first-frame env)))
        (scan (frame-variables frame) (frame-values frame)))))
  (env-loop env))

(define (define-variable! var val env)

  ; DEBUG BEGIN;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if DEBUG (begin
              (display "define-variable!:\t")(display "var = ")(display var)
              (display "\tval = ")(display val)(display "\tenv = ")
              (display env)(newline)))
  ; DEBUG END;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars) (add-binding-to-frame! var val frame))
            ((eq? var (car vars)) (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame) (frame-values frame))))




