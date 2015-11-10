; Singleton design pattern

(define SingleObject 
  (begin
    ; static members
    (define mBuilt #f)
    (define mInstance #f)
    (define (init)
      (if (eq? #t mBuilt) 
        (display "SingleObject: cannot create instance\n")
        (set! mBuilt #t)))
    (define (getInstance)
      (if (eq? #f mInstance) (set! mInstance (new)))
      mInstance)
    (define (new)
      (init)
      this)
     (define (interface m)
      (cond ((eq? m 'getInstance) (getInstance))
            ((eq? m 'showMessage) (showMessage interface))
            ((eq? m 'new)(new))
            (else (display "SingleObject: unknown operation error\n"))))
    ;
    (lambda ()
    ; members
    (define (showMessage self)
      (display "The single object is alive and well\n"))
    ;
    interface)))

(define obj ((SingleObject) 'getInstance))

