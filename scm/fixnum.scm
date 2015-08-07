(define x
  (let loop ((n 1))
    (if (fixnum? n) (loop (* 2 n)) (- n 1))))

(define y (- (expt 2 57) 1))
