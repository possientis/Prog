(use-modules (system vm program))

(define (f x) (* x x))

(display (program? f))(newline) ; is f a compiled procedure?


(display "bytes codes = ")(display (program-objcode f))(newline)
(display "objects = ")(display (program-objects f))(newline)
(display "module = ")(display (program-module f))(newline)
(display "free vars = ")(display (program-free-variables f))(newline)
(display "meta = ")(display (program-meta f))(newline)
(display "bindings = ")(display (program-bindings f))(newline)
(display "sources = ")(display (program-sources f))(newline)


