;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-cond)) 
  (begin
    (define included-cond #f)
    (display "loading cond")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "begin.scm")

; testing
(define (cond? exp) (tagged-list? exp 'cond))


; destructuring
(define (cond-predicate clause) (car clause))

(define (cond-clauses exp) (cdr exp))

; eval
(define (eval-cond exp env)
  (eval (cond->if exp) env))

; analyze 
(define (analyze-cond exp)
  (analyze (cond->if exp)))



(define (cond->if exp) 
  (expand-clauses (cond-clauses exp)))


(define (expand-clauses clauses)
  (if (null? clauses)
    '#f ; returning symbol '#f (an expresssion) which is not #f (a value)
    (let ((first (car clauses))
          (rest (cdr clauses)))
      (if (cond-else-clause? first)
        (if (null? rest)
          (make-begin (cond-actions first))
          (error "ELSE clause isn't last -- COND->IF" clauses))
        (make-if (cond-predicate first)
                 (make-begin (cond-actions first))
                 (expand-clauses rest))))))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-actions clause) (cdr clause))


))  ; include guard

