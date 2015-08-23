(define (bar a b c . d)
  (newline)
  (display d)
  (newline))

(bar 1 2 3 4 5 6 7 8 9)

(define foo
  (lambda arg
    (newline)
    (display arg)
    (newline)))

(foo 1 2 3 4 5 6 7 8 9)
