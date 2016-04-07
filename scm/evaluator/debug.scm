(display "running debug\n")
(load "primitive.scm")
(load "environment.scm")
;(load "apply.scm")
(load "eval.scm")                    ; uncomment in scm

(display primitive-procedures)(newline)

(define first (car primitive-procedures))

(define seq (list first))

(newline)(display seq)(newline)

(newline)(display "apply-primitive = ")(display apply-primitive)(newline)
(newline)(display "apply = ")(display apply)(newline)
(newline)(display "eval-primitive = ")(display eval-primitive)(newline)
(newline)(display "eval = ")(display eval)(newline)


(newline)(display "map = ")(display map)(newline)
(eval '(map car seq) global-env)      ; uncomment in scm
;(map car seq)                         ; uncomment in interpreter

; attempting to replicate interpreter error from the scm thread
; has eval one single argument or 2 arguments? ---> key question I think


