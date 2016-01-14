(load "make.scm")

(define (or? exp) (tagged-list? exp 'or))

(define (or-predicates exp) (cdr exp))

(define (expand-or-predicates predicates)
  (if (null? predicates)
    '#f ; returning symbol '#f which will be evaluated to #f
    (let ((first (car predicates))
          (rest (cdr predicates)))
      (if (null? rest)
        first
        (make-if first '#t (expand-or-predicates rest))))))


(define (or->if exp)
  (expand-or-predicates (or-predicates exp)))
