;; Return value is undefined unless n is a non-negative integer
;; (fact 0) => 1
;; (fact 1) => 1

(define (fact n)
  (let loop ((prod 1) (x n))
    (if (< x 2)
      prod
      (loop (* prod x) (- x 1)))))
