(define (unless condition usual-value exceptional-value)
  (if condition exception-value usual value))

; scheme is strict not lazy, so all arguments of 'unless'
; are evaluated prior to the execution of the function's
; body leading to an infinite recursion and stack overlow

(define (factorial n)
  (unless (= n 1) (* n (factorial (- n 1))) 1))

