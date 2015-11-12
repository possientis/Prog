; Singleton design pattern

(define SingleObject
  (begin
    ; static interface
    (define (static m)
      (cond ((eq? m 'new) (new)) ; 'new' instead of '(new)' if 'data' involved
            ((eq? m 'getInstance)(getInstance))
            (else (display "SingleObject: unknown static operation error\n"))))
    ; instance interface
    (define (this)  ; (this data) when applicable
      (lambda (m)
        (cond ((eq? m 'showMessage)(showMessage)) ; (showMessage data)
              (else (display "SingleObject: unknown instance operation error\n")))))
    ; static data
    (define mBuilt #f)
    (define mInstance #f)
    ; class members
    (define (getInstance)
      (if (eq? #f mInstance) (set! mInstance (SingleObject 'new)))
      mInstance)
    ;
    (define (new)
      (if (eq? #t mBuilt)
        (begin (display "SingleObject: cannot create new instance\n") #f)
        (begin (set! mBuilt #t) (this))))
    ; instance members
    (define (showMessage)
      (display "The single object is alive and well\n"))
    ; returning static interface
    static))

; call will succeed but subsequent call to 'getInstance' will fail
;(define obj (SingleObject 'new))

(define object1 (SingleObject 'getInstance))
(object1 'showMessage)

(define object2 (SingleObject 'getInstance))
(if (eq? object1 object2) (display "The two objects are the same\n"))

(exit 0)

