(load "main.scm")

(set-debug #t)

(define expr '3)

(set-eval-mode 'strict)

(display (lazy-eval '3))(newline)

(define x (lazy-eval '3))

;(list? x)



(exit 0)
