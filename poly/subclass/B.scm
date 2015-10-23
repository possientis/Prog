; B.scm
(load "A.scm")

(define B   ; constructor of class 'B' (built to derive from 'A')
  ; private static member
  (let ((swap
          (lambda (x y)             ; swapping two B-objects
            (((A) 'swap) x y)       ; swapping base onjects
            (let ((temp (x 'bGet)))
              ((x 'bSet) (y 'bGet))
              ((y 'bSet) temp)))))
  ;
  ;  (normal identation ignored)
  ;
  (lambda args  ; syntax args rather than (args), allowing for missing argument
  ;
  ; data
  (define base #f)  ; base object
  (define b_ #f)
  ;
  ; argument args is expected to be of three possible forms
  ; 1. args = '() : empty constructor, returning object for static member call
  ; 2. args = '(x y) : list containing two integers. Normal constructor
  ; 3. args = '(b)   : list containing a single B-object. Copy constructor
  ; Like in Python, we do not have support for method overloading
  ; hence construction of object requires more work
  (define (init)
    (if (null? args)                ; empty contructor
      (set! base (A))               ; building empty base, to access static members
      ; else
      (if (null? (cdr args))        ; single argument -> copy ctor
        (let ((rhs (car args)))
          (set! base (A rhs))       ; calling base copy ctor for A on B-object rhs
          (set! b_ (rhs 'bGet)))
        ; else
        (begin                      ; two arguments -> normal ctor
          (set! base (A (car args)))
          (set! b_ (cadr args)))))) ; b_ is a single element list, hence 'car'
  ; interface
  (define (this m)
    (cond ((eq? m 'bGet) (bGet))
          ((eq? m 'bSet) bSet)
          ((eq? m 'foo)(foo)) ; override
          ((eq? m 'swap) swap); static, use syntax (((B) 'swap) x y)
          (else (base m))))   ; passing message to base object
  ; implementations
  ;
  (define (bGet)
    b_)
  ;
  (define (bSet value)
    (set! b_ value))
  ;
  (define (foo)
    (display "B::foo() is running\n"))
  ; initializing object
  (init)
  ; returning interface
  this)))


