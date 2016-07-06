;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-cond)) 
  (begin
    (define included-cond #f)
    (display "loading cond")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

; destructuring
(define (cond-clauses exp) (cdr exp))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))


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
    #f
    (let ((first (car clauses))
          (rest (cdr clauses)))
      (if (cond-else-clause? first)
        (if (null? rest)
          (make-begin (cond-actions first))
          (error "ELSE clause isn't last -- COND->IF" clauses))
        (make-if (cond-predicate first)
                 (make-begin (cond-actions first))
                 (expand-clauses rest))))))

))  ; include guard

