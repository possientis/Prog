(define (make-if predicate consequent alternative) 
  (list 'if predicate consequent alternative))

(define (make-not predicate) (list 'not predicate))

(define (make-lambda parameters body) (cons 'lambda (cons parameters body)))

(define (make-begin operands) (cons 'begin operands))

(define (make-let bindings body) (cons 'let (cons bindings body)))





