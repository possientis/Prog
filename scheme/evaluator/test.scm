; loading interpreter
(load "main.scm") 

; loading interpreter into global-env
(force-thunk (lazy-eval '(load "main.scm")))

; global-env should now have strict-eval , + etc...
(newline)
(display "strict-eval = ")(display (strict-eval 'strict-eval))(newline)
(newline)
(display "+ = ")(display (strict-eval '+))(newline)
(newline)
(display "primitives are: ")(display (strict-eval 'primitive-procedures))(newline) 

; and global-env should also have a global-env
(newline)
(display "global-env = ")(display (strict-eval '(global-env 'to-string)))(newline)


(newline)
(display "global-env::string->symbol = ")
(display (strict-eval '((global-env 'lookup) 'string->symbol)))(newline)


(newline)
(display "global-env::+ = ")
; this fails
(display (strict-eval '((global-env 'lookup) '+)))(newline)

; yet this fails
;(strict-eval '(strict-eval '+))


(exit 0)



;string->symbol, vector-fill!, symbol?, vector-ref, string?, string-append, vector-length, vector-set!

