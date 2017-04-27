(define (f x) (* x x))
(define (g) (display "hello world!\n"))

(display (procedure? f))      ; #t
(display (thunk? f))          ; #f
(display (thunk? g))          ; #t
(display (procedure-name f))  ; f
(display (symbol? (procedure-name f)))  ; #t
(display (procedure-source f)); #f (not available)
(display (procedure-properties f))

