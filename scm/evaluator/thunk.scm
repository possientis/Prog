;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-thunk)) 
  (begin
    (define included-thunk #f)
    (display "loading thunk")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(define thunk   ; constructor
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'value) (value data))
              ((eq? m 'thunk?) #t)
              (else (error "thunk: unknown operation error" m)))))
    ;
    (define (expression data) (cadr data))
    ;
    (define (environment data) (caddr data))
    ;
    (define (evaluated? data) (null? (environment data)))
    ;
    (define (value data)
      (let ((expr (expression data))
            (env  (environment data)))
        (if (evaluated? data)
          (if (self-evaluating? expr) expr (error "no environment for thunk" expr)) 
          (let ((value (new-eval expr env)))
            (set-car! (cdr data) value) ; replacing expression by its value
            (set-car! (cddr data) '())  ; discarding environment for gb release
            value))))

    ;
    ; returning two argument constructor
    ;
    (lambda (expr env) (this (list 'data expr env)))))

))  ; include guard


