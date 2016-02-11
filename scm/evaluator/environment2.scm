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
        (if (empty? data) (set-cdr! data (list (frame)))) ; adding first frame
        (let ((frame (first-frame data)))
          ((frame 'insert!) var val))))
    ;
    (define (lookup data)
      (lambda (var)
        (define (loop env)
          (if (empty? env)
            (error "Unbound variable -- LOOKUP" var)
            (let ((frame (first-frame env)))
              (let ((varval ((frame 'find) var)))
                (if (eq? #f varval) ; var not in current frame
                  (loop (enclosing-environment env))
                  (cdr varval)))))) ; varval is pair (var . val)
        (loop data)))
        
    ;
    (define (set-var! data)
      (lambda (var val)
        (define (env-loop env)
          (if (empty? env)
            (error "Unbound variable -- SET!" var)
            (let ((frame (first-frame env)))
              (let ((found ((env 'find) var)))
                (if (eq? #f found) ; var not in current frame
                  (env-loop (enclosing-environment env))
                  ((env 'insert!) var val))))))
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







