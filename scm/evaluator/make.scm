;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-make)) 
  (begin
    (define included-make #f)
    (display "loading make")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(define (make-if predicate consequent alternative) 
  (list 'if predicate consequent alternative))

(define (make-not predicate) (list 'not predicate))

(define (make-begin operands) (cons 'begin operands))

(define (make-let bindings body) (cons 'let (cons bindings body)))

(define (make-lambda parameters body) (cons 'lambda (cons parameters body)))

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

))  ; include guard
