(define-values (x y) (values 34 'foo))

(display "x = ")(display x)(newline)  ; x = 34
(display "y = ")(display y)(newline)  ; y = foo


(define-values (x . y) (values 34 'foo 'bar))


(display "x = ")(display x)(newline)  ; x = 34
(display "y = ")(display y)(newline)  ; y = (foo bar)


