;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-and)) 
  (begin
    (define included-and #f)
    (display "loading and")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "if.scm")

; testing
(define (and? exp) (tagged-list? exp 'and))

; destructuring
(define (and-predicates exp) (cdr exp))

; eval
(define (eval-and exp env)
  (eval (and->if exp) env))

; analyze
(define (analyze-and exp)
  (analyze (and->if exp)))


(define (and->if exp)
  (expand-and-predicates (and-predicates exp)))

(define (expand-and-predicates predicates)
  (if (null? predicates)
    '#t ; returning symbol '#t which will be evaluated to #t
    (let ((first (car predicates))
          (rest (cdr predicates)))
      (if (null? rest)
        first
        (make-if (make-not first) '#f (expand-and-predicates rest))))))

))  ; include guard
