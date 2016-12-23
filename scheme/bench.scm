(define (bench action iterations)
  (if (<= iterations 0)
    'done
    (begin
      (action)
      (bench action (- iterations 1)))))

(define (nop)
  'done)

(bench nop 1000000)

(exit 0)
