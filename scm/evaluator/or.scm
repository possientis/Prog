;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-or)) 
  (begin
    (define included-or #f)
    (display "loading or")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "if.scm")

; testing
(define (or? exp) (tagged-list? exp 'or))


; destructuring
(define (or-predicates exp) (cdr exp))

; eval
(define (eval-or exp env)
  (eval (or->if exp) env))

; analyze
(define (analyze-or exp)
  (analyze (or->if exp)))


(define (or->if exp)
  (expand-or-predicates (or-predicates exp)))

(define (expand-or-predicates predicates)
  (if (null? predicates)
    #f 
    (let ((first (car predicates))
          (rest (cdr predicates)))
      (if (null? rest)
        first
        (make-if first #t (expand-or-predicates rest))))))

))  ; include guard

