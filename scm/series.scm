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







