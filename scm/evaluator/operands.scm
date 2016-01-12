(define (list-of-values operands env)
  (if (no-operands? operands) '()
    (cons (eval (first-operand operands) env)                       
          (list-of-values (rest-operands operands) env))))      

(define (no-operands? operands) (null? operands))

(define (first-operand operands) (car operands))

(define (rest-operands operands) (cdr operands))

(define (last-operand? operands) (null? (cdr operands)))

(define (eval-sequence operands env)
  (cond ((last-operand? operands) (eval (first-operand operands) env))          
        (else (eval (first-operand operands) env)
              (eval-sequence (rest-operands operands) env))))           




