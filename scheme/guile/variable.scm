
(define x (make-undefined-variable))

(display x)(newline)  ; #<variable 558d6cc4ed50 value: #<undefined>>

(define y (make-variable 5))

(display y)(newline)  ; #<variable 558d6cc4ed40 value: 5>

(display (variable-bound? x))(newline)  ; #f  x == NULL
(display (variable-bound? y))(newline)  ; #t  y != NULL 

(display (variable-ref y))(newline)     ; 5   *y

(variable-set! x 10)                    ; x = new int(10)
(display (variable-bound? x))(newline)  ; #t  x != NULL
(display (variable-ref x))(newline)     ; 10   *x

(variable-unset! x)
(display (variable-bound? x))(newline)  ; #f  x == NULL

(display (variable? x))(newline)        ; #t
(display (variable? y))(newline)        ; #t
