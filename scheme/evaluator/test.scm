(define flag #t)

(define (test) 
  (display "test is running\n"))


(define (try a) 
  (display "try is running\n"))

(display (try (test)))

(exit 0)


