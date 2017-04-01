(define (valid-code-point? n)
  (or (and (<= 0 n) (<= n #xd7ff))
      (and (<= #xe000 n) (<= n #x10ffff))))

(display (integer->char #x41))(newline)
(display (valid-code-point? #x41))(newline)

(exit 0)
