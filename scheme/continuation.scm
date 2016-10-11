(define the-continuation #f)

(define (test)
  (let ((i 0))
    (display "running just before 'call-with-current-continuation\n")
    (call-with-current-continuation
      (lambda (k)
        (display "running just before saving continuation\n")
        (set! the-continuation k)
        (display "running just after saving continuation\n")))
    (display "running just after 'call-with-current-continuation\n")
    (set! i (+ i 1))
    i))

(display "calling (test) ...\n")
(display (test))(newline)
(newline)
(display "calling (the-continuation 0) 4 times ...\n")
(display (the-continuation 0))(newline)  ; not sure what the argument does
(display (the-continuation 0))(newline)  ; not sure what the argument does
(display (the-continuation 0))(newline)  ; not sure what the argument does
(display (the-continuation 0))(newline)  ; not sure what the argument does

(exit 0)

