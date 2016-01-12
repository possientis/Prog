(load "operands.scm")
(load "if.scm")       ; make-if
(load "begin.scm")    ; make-begin

(define (cond? exp) (tagged-list? exp 'cond)) ; tagged-list? in eval.scm

(define (cond->if exp) 
  (expand-clauses (cond-clauses exp)))

(define (cond-clauses exp) (cdr exp))

(define (expand-clauses clauses)
  (if (null? clauses)
    '#f ; returning symbol '#f (an expresssion) which is not #f (a value)
    (let ((first (car clauses))
          (rest (cdr clauses)))
      (if (cond-else-clause? first)
        (if (null? rest)
          (sequence->exp (cond-actions first))
          (error "ELSE clause isn't last -- COND->IF" clauses))
        (make-if (cond-predicate first)
                 (sequence->exp (cond-actions first))
                 (expand-clauses rest))))))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (sequence->exp sequence)
  (cond ((null? exps) sequence)
        ((last-operand? sequence) (first-operand sequence)) 
        (else (make-begin sequence))))          

(define (cond-actions clause) (cdr clause))

(define (cond-predicate clause) (car clause))

