(load "main.scm")

(define expr (make-thunk 3 '()))

(display (strict-eval expr) (newline))
