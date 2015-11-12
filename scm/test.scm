(define (Loop10 I)
  (if (= I 10)
    'skip
    (begin
      (display I)(newline)
      (Loop10 (+ I 1)))))

(Loop10 0)
