(define (fast-expt b n)
  (cond ((= n 0) 1)
        ((even? n) (fast-expt (* b b) (/ n 2)))
        ((odd? n) (* b (fast-expt b (- n 1))))
        (else (display "fast-expt: unexpected argument\n"))))


(define (fast-expt2 b n)
  (let loop ((b b) (n n) (prod 1))
    (cond ((= n 0) prod)
          ((even? n) (loop (* b b) (/ n 2) prod))
          ((odd? n) (loop b (- n 1) (* b prod)))
          (else (display "fast-expt: unexpected argument\n")))))
