; one possible implementation of environment
(load "frame")

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
        (if (empty? data) (set-cdr! data (list (frame)))) ; adding first frame
        (let ((current (first-frame data)))
          ((current 'insert!) var val))))
    ;
    (define (lookup data)
      (lambda (var)
        (let loop ((env data))
          (if (empty? env)
            (error "Unbound variable -- LOOKUP" var)
            (let ((current (first-frame env)))
              (let ((varval ((current 'find) var)))
                (if (eq? #f varval) ; var not in current frame
                  (loop (enclosing-environment env))
                  (cdr varval)))))))) ; varval is pair (var . val)
    ;
    (define (set-var! data)
      (lambda (var val)
        (let env-loop ((env data))
          (if (empty? env)
            (error "Unbound variable -- SET!" var)
            (let ((current (first-frame env)))
              (let ((found ((current 'find) var)))
                (if (eq? #f found) ; var not in current frame
                  (env-loop (enclosing-environment env))
                  ((current 'insert!) var val))))))))
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
    ; Private helper functions
    ;
    (define (enclosing-environment data) (cons 'data (cddr data)))
    ;
    (define (first-frame data) (cadr data))
    ;
    (define (make-frame vars vals)
      (let ((new-frame (frame)))            ; empty-frame
        (let loop ((vars vars) (vals vals))
          (if (null? vars)
            new-frame
            ;else
            (begin
              ((new-frame 'insert!) (car vars) (car vals))
              (loop (cdr vars) (cdr vals)))))))
    ;
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (cons 'data '())))))

; just completed delete! in frame1.scm





