(define (mysqrt x)
  (let ((improve
          (lambda (guess x) (/ (+ guess (/ x guess)) 2.0)))
        (good-enough?
          (lambda (guess x) (< (/(abs (- x (* guess guess))) x) 0.00001))))
    (letrec (
        (sqrt-iter
          (lambda (guess x)
            (if (good-enough? guess x)
              guess
              (sqrt-iter (improve guess x) x)))))
    (sqrt-iter 1.0 x))))
