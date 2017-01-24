(define lst (list 'a 'b 'c))

(@apply (lambda (v1 v2 v3) (set! v1 (cons v2 v3))) lst)

; compare this with apply
(display lst)(newline)  ; ((b . c) b c)
