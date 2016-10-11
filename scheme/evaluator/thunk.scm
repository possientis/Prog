;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-thunk)) 
  (begin
    (define included-thunk #f)
    (display "loading thunk")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (thunk? obj) 
  (tagged-list? obj 'thunk))

; making
(define thunk   ; constructor
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'value) (value data))
              (else (error "thunk: unknown operation error" m)))))
    ;
    (define (expression data) (cadr data))
    ;
    (define (environment data) (caddr data))
    ;
    (define (evaluated? data) (null? (environment data)))
    ;
    ; This function is called when a thunk is forced. An evaluation of the
    ; thunk needs to take place and the question naturally arises of which 
    ; evaluation function to call. We cannot use 'new-eval` as this would
    ; fail to do anything when eval-mode is 'lazy'. Hence we need to use
    ; either 'strict-eval' or 'analyze'.
    (define (value data)
      (let ((expr (expression data))
            (env  (environment data)))
        (if (evaluated? data)
          expr
          (let ((value (strict-eval expr env)))
            (set-car! (cdr data) value) ; replacing expression by its value
            (set-car! (cddr data) '())  ; discarding environment for gb release
            value))))
    ;
    ; returning two argument constructor
    ;
    (lambda (expr env) (list 'thunk (this (list 'data expr env))))))

; forcing
(define (force-thunk obj)
  (display "check9: force-thunk: cannot evaluate object\n")
  (if (thunk? obj) 
    ((cadr obj) 'value)
    (error "force-thunk: object not a thunk")))


))  ; include guard


