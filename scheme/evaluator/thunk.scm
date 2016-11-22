;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-thunk)) 
  (begin
    (define included-thunk #f)
    (display "loading thunk")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (thunk? obj) (tagged-list? obj 'thunk))

; making
(define make-thunk   ; constructor
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'value) (value data))
              ((eq? m 'expression) (expression data))
              ((eq? m 'environment) (environment data))
              ((eq? m 'evaluated?) (evaluated? data))
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
    (lambda (expr env) 
      (if (thunk? expr) ; do not create a double thunk
        expr
        (list 'thunk (this (list 'data expr env)))))))

; destructuring
(define (thunk-expression obj) ((cadr obj) 'expression))
(define (thunk-environment obj) ((cadr obj) 'environment))
(define (thunk-evaluated? obj) ((cadr obj) 'evaluated?))

; strict eval
(define (strict-eval-thunk exp env) ((cadr exp) 'value))

; analyze
(define (analyze-thunk exp) (lambda (env) ((cadr exp) 'value)))

; lazy eval
(define (lazy-eval-thunk exp env) exp)

; Note that we do not throw an error when argument to force-thunk is not a 
; thunk. This has the disadvantage of removing possible detection of logic
; errors. However, considering we are mixing various types of evaluations
; (strict, lazy, analyze), the logic is not very clear anyway, and we often
; end up with unexpected thunks in the evaluation process. This laxed semantics 
; of force-thunk allows us to remove possible thunks in a list of arguments. 
; (See the module primitive-procedure)
; forcing
(define (force-thunk obj)
  (if (thunk? obj) ((cadr obj) 'value) obj))

))  ; include guard

