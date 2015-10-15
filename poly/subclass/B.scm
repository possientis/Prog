(load "A.scm")

(define (B x . y)
  ; data
  (define base #f)  ; base object
  ; construction
  (define (init)
    (if (null? y) ; single argument -> copy ctor
      (begin
        (set! base (A x)) ; calling copy ctor for A. x is B-object, also A-object
        (set! y (x 'b)))
      (begin      ; two arguments -> normal ctor
        (set! base (A x))
        (set! y (car y)))))
  ; interface
  (define (this m)
    (cond ((eq? m 'b) y)
          ((eq? m 'foo)(foo)) ; override
          (else (base m))))   ; passing message to base object
  ; implementations
  (define (foo)
    (display "B::foo() is running\n"))
  ; initializing object
  (init)
  ; returning interface
  this)


