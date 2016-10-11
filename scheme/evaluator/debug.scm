(load "main.scm")

(define expr (thunk 3 '()))

(display (strict-eval expr))(newline)
