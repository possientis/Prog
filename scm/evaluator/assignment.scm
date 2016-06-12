;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-assignment)) 
  (begin
    (define included-assignment #f)
    (display "loading assignment")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (assignment? exp) (tagged-list? exp 'set!))

; destructuring
(define (assignment-variable exp) (cadr exp))
(define (assignment-expression exp) (caddr exp))

; eval
(define (eval-assignment exp env)
  (let ((var (assignment-variable exp))
        (rhs (assignment-expression exp)))
    (let ((val (eval rhs env)))
      ((env 'set!) var val))))

; analyze
(define (analyze-assignment exp)
  (let ((var (assignment-variable exp))
        (rhs (assignment-expression exp)))
    (let ((val (analyze rhs)))
      (lambda (env) ((env 'set!) var (val env))))))

))  ; include guard
