(define (factorial n)
  (let loop ((n n) (acc 1))
    (if (<= n 1)
      acc
      (loop (- n 1) (* n acc)))))


(display (factorial 100000))(newline)
