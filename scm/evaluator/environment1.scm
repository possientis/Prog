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
              ((eq? m 'to-string) (to-string data))
              (else (error "environment2: unknown operation error: " m)))))
    ;
    ; Implementation of public interface
    ;
    ; empty environment represented by the pair ('data . '())
    ; rather than simply '() so as to make it mutable
    (define (empty? data)
      (let frame-loop ((env (cdr data)))
        (if (null? env) #t              
          (let ((current (car env)))      ; else
            (if (not (current 'empty?)) #f                        
              (frame-loop (cdr env))))))) ; else
    ;
    (define (to-string data)
      (let frame-loop ((env (cdr data)) (out "{") (i 0))
        (if (null? env) (string-append out "}")
          (let ((current (car env)))
            (let ((new-out (string-append
                             out
                             (if (= 0 i) "frame " ", frame ")
                             (number->string i)
                             ": "
                             (current 'to-string))))
              (frame-loop (cdr env) new-out (+ i 1)))))))
    ; 
    ; only add binding to current frame, potentially overwrites existing binding
    (define (define! data)
      (lambda (var val)
        (if (empty? data) (set-cdr! data (list (frame)))) ; adding first frame
        (let ((current (cadr data)))
          ((current 'insert!) var val))))
    ;
    (define (lookup data)
      (lambda (var)
        (let frame-loop ((env (cdr data)))
          (if (null? env)
            (error "Unbound variable -- LOOKUP" var)
            (let ((current (car env)))
              (let ((varval ((current 'find) var)))
                (if (eq? #f varval) ; var not in current frame
                  (frame-loop (cdr env))
                  (cdr varval)))))))) ; varval is pair (var . val)
    ;
    ; overwrites binding in top-most frame where name is visible
    (define (set-var! data)
      (lambda (var val)
        (let frame-loop ((env (cdr data)))
          (if (null? env)
            (error "Unbound variable -- SET!" var)
            (let ((current (car env)))
              (let ((found ((current 'find) var)))
                (if (eq? #f found) ; var not in current frame
                  (frame-loop (cdr env))
                  ((current 'insert!) var val))))))))

    ;
    (define (delete! data)
      (lambda (var)
        (let frame-loop ((env (cdr data)))
          (if (not (null? env)) ; delete! has no impact if var not found
            (let ((current (car env)))
              (let ((found ((current 'find) var)))
                (if (eq? #f found)  ; var not in current frame
                  (frame-loop (cdr env))
                  ((current 'delete!) var))))))))  ; remove binding in frame
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
    (define (display-env data) 'TBI)
    ;
    ; Private helper functions
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
    ; returning no argument constructor
    ;
    (lambda () (this (cons 'data '())))))


