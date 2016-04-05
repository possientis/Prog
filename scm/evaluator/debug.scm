(display "running debug\n")
(load "primitive.scm")
(load "environment.scm")
;(load "apply.scm")

(display primitive-procedures)(newline)

(define first (car primitive-procedures))

(define seq (list first))

(newline)(display seq)(newline)

(newline) (display apply)(newline)

(map car seq)



