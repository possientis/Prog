(load "make.scm")

(define (and? exp) (tagged-list? exp 'and))

(define (and-predicates exp) (cdr exp))

(define (expand-and-predicates predicates)
  (if (null? predicates)
    '#t ; returning symbol '#t which will be evaluated to #t
    (let ((first (car predicates))
          (rest (cdr predicates)))
      (if (null? rest)
        first
        (make-if (make-not first) '#f (expand-and-predicates rest))))))

(define (and->if exp)
  (expand-and-predicates (and-predicates exp)))

