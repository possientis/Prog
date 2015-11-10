(define A ; class constructor
  (begin
  ; interface
  (define (this data)
    (lambda (m)
      (cond ((eq? m 'foo) (display "A::foo() is running\n"))
            ((eq? m 'get) data)
            (else (display "A: unkown operation error\n")))))
  ; creating instance
  (lambda (data)
    (this data))))


(define x (A 3))

(x 'foo)
(display (x 'get))(newline)
