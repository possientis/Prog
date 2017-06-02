(define env (interaction-environment))

(display (eval '(+ 1 2) env))(newline)

(display (primitive-eval '(+ 1 2)))(newline)


(exit 0)
