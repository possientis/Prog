(define the-continuation #f)

(define (test)
  (let ((i 0))
;    (display "running just before 'call-with-current-continuation\n")
    (define ret (call-with-current-continuation
      (lambda (k)
        (display "running just before saving continuation\n")
        (set! the-continuation k)
        (display "running just after saving continuation\n"))))
    (display "running just after 'call-with-current-continuation: ret = ")
    (display ret)(newline)
    (set! i (+ i 1))
    i))

(display "calling (test) ...\n")
(display (test))(newline)
(newline)
(display "calling (the-continuation 0) 4 times ...\n")
(display (the-continuation 12))(newline)  ;  
(display (the-continuation 15))(newline)  ; not sure what the argument does
(display (the-continuation 19))(newline)  ; not sure what the argument does
(display (the-continuation -23))(newline)  ; not sure what the argument does

(exit 0)

