;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-environment1)) 
  (begin
    (define included-environment1 #f)
    (display "loading environment1")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


; one possible implementation of environment
(load "frame.scm")

(define environment1    ; constructor
  (let ()               ; name encapsulation
    ; object built from data is message passing interface
    (define (this data) ; data ignored here
      (lambda(m)
        (cond ((eq? m 'empty?)(empty? data))
              ((eq? m 'define!)(define! data))
              ((eq? m 'lookup)(lookup data))
              ((eq? m 'defined?)(is-defined data))
              ((eq? m 'set!)(set-var! data))
              ((eq? m 'delete!)(delete! data))
              ((eq? m 'extended)(extended data))  ; returns extended env
              ((eq? m 'to-string) (to-string data))
              (else (error "environment1: unknown operation error: " m)))))
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
    (define (is-defined data)
      (lambda (var)
        (let frame-loop ((env (cdr data)))
          (if (null? env)
            #f
            (let ((current (car env)))
              (let ((varval ((current 'find) var)))
                (if (eq? #f varval) ; var not in current frame
                  (frame-loop (cdr env))
                  #t)))))))
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
        ; returning new environment instance, with additional frame
        (let ((new-frame (make-frame vars vals)))
          (this (cons 'data (cons new-frame (cdr data)))))))
    ;
    (define (display-env data) 'TODO)
    ;
    ; Private helper functions
    ;
    (define (make-frame vars vals)
      (let ((new-frame (frame)))            ; empty-frame
        (let loop ((vars vars) (vals vals))
          (cond ((null? vars) new-frame)
                ((symbol? vars) ((new-frame 'insert!) vars vals) new-frame)
                (else ((new-frame 'insert!) (car vars) (car vals))
                      (loop (cdr vars) (cdr vals)))))))
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (cons 'data '())))))


))  ; include guard
