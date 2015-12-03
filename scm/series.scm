(load "stream.scm")

; good old factorial
(define (fact n)
  (let loop ((n n) (a 1))
    (if (< n 1) a
      ; else
      (loop (- n 1) (* n a)))))

; exponential series: calculating factorial of large integer is a bad
; practice. (series-eval series-exp-naive 1 1000) is very slow and fails.
; See a far better implementation of exponential series below as 'series-exp'
(define series-exp-naive
  (stream-map 
    (lambda (n) (/ 1 (fact n)))
    (integers-from 0)))
; 1 1/2 1/3 ...
(define series-inv
  (stream-map
    (lambda (n) (/ 1 n))
    (integers-from 1)))

; s(x) approximated with num terms
(define (series-eval2 s x num)
  (if (= 0 num) 0
    ; else
    (+ (s 'car) (* x (series-eval2 (s 'cdr) x (- num 1))))))

; stack friendly, but not as nice when looking at the code. However, this 
; implementation can withstand a call to (series-eval series-exp 1 1000000)
; unlike the series-eval2 implementation which fails at 50000 !!!
(define (series-eval s x num)
  (let loop ((s s) (num num) (sum 0) (z 1))
             (if (= 0 num) sum
               ; else
               (loop (s 'cdr) (- num 1) (+ sum (* (s 'car) z)) (* z x)))))

(define (series-integrate s)
  (stream-mul s series-inv))

; altenative definition of series-exp-naive: way better
(define series-exp
  (stream-cons 1 (series-integrate series-exp)))


; the derivative of sine is cosine, sine(0) = 0
(define series-sin
  (stream-cons 0 (series-integrate series-cos)))

; the derivative of cosine is minus sine, cosine(0) = 1
(define series-cos
  (stream-cons 1 (series-integrate (stream-scale series-sin -1))))

(define (series-mul s1 s2)
  (stream-cons 
    (* (s1 'car) (s2 'car))               ; s1(0).s2(0)
    (stream-add
      (stream-scale (s2 'cdr) (s1 'car))  ; (s2(1) + x.s2(2) + ... ). s1(0)
      (series-mul (s1 'cdr) s2))))        ; (s1(1) + x.s1(2) + ... ). s2 

(define series-check  ; should be 1 + 0x + 0x^2 + ...
  (stream-add
    (series-mul series-sin series-sin)
    (series-mul series-cos series-cos)))

; looking for t such that s.t = 1 + 0.x + 0.x^2 + ...
; which is (s(0) + x.(s(1) + ...)).t = 1
; hence the recursive formula: t = s(0)^(-1).[1 - x.s'.t]
; where s' = (s(1) + s(2)x + ...) = (s 'cdr)
(define (series-inverse s)      ; need s(0) != 0
  (stream-scale
    (stream-cons 1 (stream-scale (series-mul (s 'cdr) (series-inverse s)) -1))
    (/ 1 (s 'car))))

(define s (series-inverse series-cos))
(define t (series-mul s series-cos))

    





