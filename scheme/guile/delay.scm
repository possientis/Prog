(define x (delay (display "I was delayed\n")))

(display (promise? x))(newline)

(force x)


(exit 0)
