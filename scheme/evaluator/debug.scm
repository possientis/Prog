(load "main.scm")

(strict-eval '(define (f) 12))

(set-eval-mode 'lazy)

(display (strict-eval '(f)))(newline)




