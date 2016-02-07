; one possible implementation of environment

(define environment2    ; constructor
  (let ((_static #f))   ; name encapsulation
    ; object built from data is message passing interface
    (define (this data) ; data ignored here
      (lambda(m)
        (cond ((eq? m 'empty?)(empty? data))
              ((eq? m 'define!)(define! data))
              ((eq? m 'lookup)(lookup data))
              ((eq? m 'set!)(set-var! data))
              ((eq? m 'extended)(extended data))  ; returns extended env
              ((eq? m 'display)(display-env data))
              (else (error "environment2: unknown operation error: " m)))))
    ;
    ; Implementation of public interface
    ;
    ; empty environment represented by the pair ('data . '())
    ; rather than simply '() so as to make it mutable
    (define (empty? data)(equal? (cdr data) '()))
    ;
    (define (define! data)
      (lambda (var val)
        (if (empty? data) (set-cdr! data (list '()))) ; adding first frame
        (let ((frame (first-frame data)))
          (define (scan pairs)
            (cond ((null? pairs) (add-binding-to-frame! var val frame))
                  ((eq? var (caar pairs)) (set-cdr! (car pairs) val))
                  (else (scan (cdr pairs)))))
          (scan frame))))
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
    (define (set-var! data)
      (lambda (var val)
        (define (env-loop data)
          (define (scan vars vals)
            (cond ((null? vars) (env-loop (enclosing-environment data)))
                  ((eq? var (car vars)) (set-car! vals val))
                  (else (scan (cdr vars) (cdr vals)))))
          (if (empty? data)
            (error "Unbound variable -- SET!" var)
            (let ((frame (first-frame data)))
              (scan (frame-variables frame) (frame-values frame)))))
        (env-loop data)))
    ;
    (define (extended data)
      (lambda (vars vals)
        (if (= (length vars) (length vals))
          ; returning new environment instance, with additional frame
          (this (cons 'data (cons (make-frame vars vals) (cdr data))))
          (if (< (length vars) (length vals))
            (error "Too many arguments supplied" vars vals)
            (error "Too few arguments supplied" vars vals)))))
    ;
    (define (display-env data)
      (display data)(newline))
    ;
    ; Private helper functions
    ;
    (define (enclosing-environment data) (cons 'data (cddr data)))
    ;
    (define (first-frame data) (cadr data))
    ;
    (define (frame-variables frame) (car frame))
    ;
    (define (frame-values frame) (cdr frame))
    ;
    (define (add-binding-to-frame! var val frame)
      (set-car! frame (cons var (car frame)))
      (set-cdr! frame (cons val (cdr frame))))
    ;
    (define (make-frame vars vals) (cons vars vals))
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (cons 'data '())))))







