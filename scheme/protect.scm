; this works but sill don't understand it.
; failing code recovers with #f return value
; However, may need to supress stdout as well as stderr

(define (protect proc)
  (lambda args
    (define result #f)
    (call-with-current-continuation
      (lambda (cont)
        (dynamic-wind (lambda () #t)
                      (lambda ()
                        (set! result (apply proc args))
                        (set! cont #f))
                      (lambda ()
                        (if cont (cont #f))))))
      result))

(define (test1)
  (error "This is an error"))

(define (divide n m)
  (quotient n m))

(define p-test (protect test1))
(define p-divide (protect divide))

(display (p-test))(newline)
(display (p-divide 1 0))(newline)

(exit 0)


