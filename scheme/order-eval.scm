;; different answers on scm and mit-scheme

(define x 5)
(define y 5)

(display "starting from x=5\n")
(define z (+ (begin (set! x 0) x) x))
(define t (+ y (begin (set! y 0) y)))
(display "(x=0) + x evaluates to :")
(display z)
(newline)
(display "x + (x=0) evaluates to :")
(display t)
(newline)

