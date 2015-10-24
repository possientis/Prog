; A.scm
(define A   ; constructor of class 'A'
  ; private static member
  (let ((swap
          (lambda (x y)             ; swapping two A-objects
            (let ((temp (x 'aGet)))
              ((x 'aSet) (y 'aGet))
              ((y 'aSet) temp)))))
  ;
  ; (normal identation ignored)
  ;
  (lambda args ; syntax args rather than (args), allowing for missing argument
  ;
  ; private data
  (define a_ #f)
  ;
  ; argument args is expected to be of three possible forms
  ; 1. args = '()   : empty constructor, returning object for static member call
  ; 2. args = '(x)  : list containing a single integer. Normal constructor
  ; 3. args = '(a)  : list containing a single A-object. Copy constructor
  ; Like in Python, we do not have support for method overloading
  ; hence construction of object requires more work
  (define (init)
    (if (not (null? args))          ; nothing done on empty constructor
      (begin
        (set! args (car args))      ; removing parenthesis around single argument
        (if (integer? args)         ; normal ctor
          (set! a_ args)
          (set! a_ (args 'aGet)))))); else copy ctor, argument is another A-object
  ;
  ; interface
  (define (this m)
    (cond ((eq? m 'aGet) (aGet))
          ((eq? m 'aSet) aSet)
          ((eq? m 'foo)(foo))
          ((eq? m 'swap) swap)      ; static, use syntax (((A) 'swap) x y)
          (else (display "A: unknown attribute error\n"))))
  ; implementations
  ;
  (define (aGet)
    a_)
  ;
  (define (aSet value)
    (set! a_ value))
  ;
  (define (foo)
    (display "A::foo() is running\n"))
  ; initializing object
  (init)
  ; returning interface
  this)))
