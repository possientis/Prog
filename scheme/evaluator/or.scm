;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-or)) 
  (begin
    (define included-or #f)
    (display "loading or")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; testing
(define (or? exp) (tagged-list? exp 'or))


; destructuring
(define (or-predicates exp) (cdr exp))

; strict eval
(define (strict-eval-or exp env)
  (strict-eval (or->if exp) env))

; analyze
(define (analyze-or exp)
  (analyze (or->if exp)))

; lazy eval
(define (lazy-eval-or exp env)
  (make-thunk exp env))

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

