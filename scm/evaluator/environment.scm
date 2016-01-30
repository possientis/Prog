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
        (cond ((eq? m 'lookup)(lookup data))
              ((eq? m 'empty?)(empty? data))
              ((eq? m 'define!)(define! data))
              ((eq? m 'set-variable-value!)(set-variable-value! data))
              ((eq? m 'extend-environment)(extend-environment data))
              ((eq? m 'display-environment)(display-environment data))
              (else (error "environment1: unknown operation error: " m)))))
    ;
    ; Implementation of public interface
    ;
    (define (lookup data)
      (lambda (var)
        (define (env-loop data)
          (define (scan vars vals)
            (cond ((null? vars) (env-loop (enclosing-environment data)))
            ((eq? var (car vars)) (car vals))
            (else (scan (cdr vars) (cdr vals)))))
          (if (empty? data)
            (error "Unbound variable" var)
            (let ((frame (first-frame data)))
              (scan (frame-variables frame) (frame-values frame)))))
        (env-loop data)))
    ;
    (define (define! data)
      (lambda (var val)
        (let ((frame (first-frame data)))
          (define (scan vars vals)
            (cond ((null? vars) (add-binding-to-frame! var val frame))
                  ((eq? var (car vars)) (set-car! vals val))
                  (else (scan (cdr vars) (cdr vals)))))
          (scan (frame-variables frame) (frame-values frame)))))
    ;
    (define (set-variable-value! data)
      'TBI)
    ;
    (define (extend-environment data)
      'TBI)
    ;
    (define (display-environment data)
      (display data)(newline))
    ;
    ; Private helper functions
    ;
    (define (empty? data)
      (equal? data (list (cons '() '()))))
    ;
    (define (enclosing-environment data) (cdr data))
    ;
    (define (first-frame data) (car data))
    ;
    (define (frame-variables frame) (car frame))
    ;
    (define (frame-values frame) (cdr frame))
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (list (cons '() '()))))))
    




(define (make-frame variables values) (cons variables values))



(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
    (cons (make-frame vars vals) base-env)
    (if (< (length vars) (length vals))
      (error "Too many arguments supplied" vars vals)
      (error "Too few arguments supplied" vars vals))))

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



