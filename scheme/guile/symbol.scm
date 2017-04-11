(define sym1 (quote hello))
(define sym2 (quote hello))
(display (eq? sym1 sym2))(newline)    ; #t

(define str1 "hello")
(define str2 "hello")
(display (eq? str1 str2))(newline)    ; #t, but may be  #f
(display (equal? str1 str2))(newline) ; #t
