(load "main.scm") ; defining analyze-eval
(strict-eval '(load "main.scm"))
(strict-eval '(strict-eval '(load "main.scm")))


(display "+ = ")(display +)(newline)

(display "+ = ")(display (strict-eval '+))(newline)

(display "+ = ")(display (strict-eval '(strict-eval '+)))(newline)

(display "+ = ")(display (strict-eval '(strict-eval '(strict-eval '+))))(newline)

;+ = #<primitive-procedure +>
;+ = (primitive-procedure #<primitive-procedure +>)
;+ = (primitive-procedure (primitive-procedure #<primitive-procedure +>))
;+ = (primitive-procedure (primitive-procedure (primitive-procedure #<primitive-procedure +>)))

(exit 0)
