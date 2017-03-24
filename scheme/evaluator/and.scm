;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-and)) 
  (begin
    (define included-and #f)
    (display "loading and")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (and? exp) (tagged-list? exp 'and))

; destructuring
(define (and-predicates exp) (cdr exp))

; strict eval
(define (strict-eval-and exp env)
  (strict-eval (and->if exp) env))

; analyze
(define (analyze-and exp)
  (analyze (and->if exp)))

; lazy eval
(define (lazy-eval-and exp env)
  (lazy-eval (and->if exp) env))

(define (and->if exp)
  (expand-and-predicates (and-predicates exp)))

(define (expand-and-predicates predicates)
  (if (null? predicates)
    #t
    (let ((first (car predicates))
          (rest (cdr predicates)))
      (if (null? rest)
        first
        (make-if (make-not first) #f (expand-and-predicates rest))))))

))  ; include guard
