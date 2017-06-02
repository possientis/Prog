(use-modules (ice-9 local-eval))


(define env
  (let ((x 100))
    (the-environment)))

(define fetch-x (local-eval '(lambda () x) env))

(display (fetch-x))(newline)  ; 100

(local-eval '(set! x 42) env)


(display (fetch-x))(newline)  ; 42


;(local-eval '(define foo 42) env)  ; no define with local-eval



(exit 0)
