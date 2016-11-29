(load "main.scm")

(set-debug #t)

(strict-eval '(define f (lambda args args)))
(define x (lazy-eval '(f 0)))
(define y (force-thunk x))
(define z (map force-thunk y))  ; needed to get expected result !!
(display z)(newline)

(strict-eval '(define (g x) (list x)))
(define u (lazy-eval '(g 5)))
(display (force-thunk u))(newline)

(define k (lambda args args))

(display (k 3))(newline)
