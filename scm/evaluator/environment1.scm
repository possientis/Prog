; one possible implementation of environment
(load "frame")

(define environment1    ; constructor
  (let ((_static #f))   ; name encapsulation
    ; object built from data is message passing interface
    (define (this data) ; data ignored here
      (lambda(m)
        (cond ((eq? m 'empty?)(empty? data))
              ((eq? m 'define!)(define! data))
              ((eq? m 'lookup)(lookup data))
              ((eq? m 'set!)(set-var! data))
              ((eq? m 'delete!)(delete! data))
              ((eq? m 'extended)(extended data))  ; returns extended env
              (else (error "environment2: unknown operation error: " m)))))
    ;
    ; Implementation of public interface
    ;
    ; empty environment represented by the pair ('data . '())
    ; rather than simply '() so as to make it mutable
    (define (empty? data)
      (equal? (cdr data) '()))
    ; 
    ; only add binding to current frame, potentially overwrites existing binding
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
    ; overwrites binding in top-most frame where name is visible
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
    (define (delete! data)
      (lambda (var)
        (let env-loop ((env data))
          (if (not (empty? env)) ; delete! has no impact if var not found
            (let ((current (first-frame env)))
              (let ((found ((current 'find) var)))
                (if (eq? #f found)  ; var not in current frame
                  (env-loop (enclosing-environment env))
                  (begin  ; else
                    ((current 'delete!) var)  ; remove binding in frame
                    (if (current 'empty?)     ; if frame empty, clean up env
                      (let ((new (remove-empty-frames data)))
                        (set-cdr! data (cdr new))))))))))))
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
    (define (remove-empty-frames data)
      (let env-loop ((env data) (new (cons 'data '())))
        (if (empty? env)
          new
          (let ((current (first-frame env)))
            (if (not (current 'empty?))
              (set! new (cons 'data (cons current (cdr new)))))
            (env-loop (enclosing-environment data) new)))))
    ;
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (cons 'data '())))))

; need to test that if bingin exists in two different frames, delete! only removes binding of top-most frame




