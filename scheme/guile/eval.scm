(define env (interaction-environment))

(display (eval '(+ 1 2) env))(newline)

(display (primitive-eval '(+ 1 2)))(newline)

(set! env (current-module))

(display (eval '(+ 1 2) env))(newline)

(display (module-variable env '+))(newline) ; #<variable 561fcc267640 value: #<procedure + (#:optional _ _ . _)>>

(module-add! env 'x (make-variable 5))

(display "x = ")(display x)(newline)

(display "x = ")(display (module-ref env 'x))(newline)




(exit 0)
