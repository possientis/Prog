(define A ; class constructor
  (begin
  ; static interface
  (define (static m)
    (cond ((eq? m 'getInstance) (getInstance))
          ((eq? m 'new) new)
          (else (display "A: unknown static operation error\n"))))
  ; instance interface
  (define (this data)
    (lambda (m)
      (cond ((eq? m 'foo) (display "A::foo() is running\n"))
            ((eq? m 'get) data)
            (else (display "A: unkown instance operation error\n")))))
  ; static data
  (define mBuilt #f)
  (define mInstance #f)
  ; static members
  (define (getInstance)
    (if (eq? #f mInstance) (set! mInstance ((A 'new) 128)))
    mInstance)
  ; creating instance
  (define (new data)
    (if (eq? #t mBuilt) 
      (begin (display "A: cannot create new instance\n") #f)
      (begin (set! mBuilt #t) (this data))))
  ; returning static interface
  static))

(define x (A 'getInstance))
(x 'foo)
(display (x 'get))(newline)

(define y (A 'getInstance))
(display (eq? x y))(newline)
(define z ((A 'new) 3))
