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
            (if 
              (k a)
              (-& n 1 (lambda (nm1)
                        (*& n a (lambda (nta)
                                  (go& nm1 nta k)))))))))

(factorial2& 5 display)(newline)






(exit 0)
