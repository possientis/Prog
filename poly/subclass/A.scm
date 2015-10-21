(define (A x)
  (define (init)
    (if (integer? x)    ; normal ctor
      'done
      (set! x (x 'a)))) ; copy ctor, argument is another A-object
  ; interface
  (define (this m)
    (cond ((eq? m 'aGet) (aGet))
          ((eq? m 'aSet) aSet)
          ((eq? m 'foo)(foo))
          (else (display "A: unknown attribute error\n"))))
  ; implementations
  ;
  (define (aGet)
    x)
  ;
  (define (aSet value)
    (set! x value))
  ;
  (define (foo)
    (display "A::foo() is running\n"))
  ; initializing object
  (init)
  ; returning interface
  this)
