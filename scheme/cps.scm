;;; continuation passing style

;;; Example 1:

(define (pyth x y)
  (sqrt (+ (* x x) (* y y))))

(display (pyth 3 4))(newline) ; 5.0

;;; need a few cps primitives

(define (+& x y k) (k (+ x y)))
(define (*& x y k) (k (* x y)))
(define (sqrt& x k) (k (sqrt x)))
(define (=& x y k) (k (= x y)))
(define (-& x y k) (k (- x y)))

;;; continuation passing style makes order of computation explicit
(define (pyth& x y k)
  (*& x x (lambda (x2)
            (*& y y (lambda (y2)
                      (+& x2 y2 (lambda (x2py2)
                                  (sqrt& x2py2 k))))))))

(pyth& 3 4 display)(newline)  ; 5.0

(define (factorial n)
  (if (= 0 n)
    1
    (* n (factorial (- n 1))))) ; not tail recursive

(display (factorial 5))(newline)

(define (factorial& n k)
  (=& 0 n (lambda (b)
            (if b
              (k 1)
              (-& n 1 (lambda (nm1)
                        (factorial& nm1 (lambda (f)
                                          (*& n f k)))))))))

(factorial& 5 display)(newline)


(define (factorial2 n) (go n 1))
(define (go n a)
  (if (= 0 n)
    a
    (go (- n 1) (* n a))))  ; tail recursive

(display (factorial2 5))(newline)

(define (factorial2& n k) (go& n 1 k))

(define (go& n a k)
  (=& 0 n (lambda (b)
            (if b 
              (k a)
              (-& n 1 (lambda (nm1)
                        (*& n a (lambda (nta)
                                  (go& nm1 nta k)))))))))

(factorial2& 5 display)(newline)

(newline)
; assume we only have cps functions, then we can recover a standard function
(define (factorial3 x)
  (factorial& x (lambda (x) x)))

(display (factorial3 5))(newline) ; 120

;;; ret = 120. But why???
;;; call-with-current-continuation has a single argument.
;;; This argument is a procedure, with a single continuation argument
;;; Now that we know about cps-functions, we are familiar with functions
;;; expecting continuations as argument: the last argument of a cps function
;;; is always a continuation (a procedure which takes a single argument).
;;; So for example:

;;; (lambda (k) (factorial& 5 k))
;;; (lambda (k) (+& 5 7))

;;; These functions take a single argument which are continuations.
;;; These functions are ideally suited to be passed to the function
;;; call-with-current-continuation.

;;; Semantics: call-with-current-continuation calls the function passed as 
;;; argument *with* the current continuation as argument.
;;; Let us denote k0 the current continuation. k0 is a procedure 
;;; which takes an argument x and then defines 'ret' as x, and 
;;; then keeps going, as per the source code of this file.

;;; (call-with-current-continuation 
;;;   (lambda (k) (factorial& 5 k)))
;;; ->
;;; (factorial& 5 k0)
;;; ->
;;; (k0 (factorial 5))
;;; ->
;;; so k0 defines 'ret' as 120 etc...
;;; ->
;;; effectively call-with-current-continuation returns the value passed to k0


(define ret 
  (call-with-current-continuation 
    (lambda (k) (factorial& 5 k))))

(display ret)(newline)

(display (call-with-current-continuation (lambda (k) (+& 5 7 k))))(newline) ; 12



(exit 0)
