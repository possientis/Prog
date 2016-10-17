(load "main.scm")

(define expr (make-thunk 3 '()))
(let ((env ((global-env 'extended) 'var expr)))
  (display (strict-eval 'var env)) (newline))



