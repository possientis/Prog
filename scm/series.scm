(load "stream.scm")

; good old factorial
(define (fact n)
  (let loop ((n n) (a 1))
    (if (< n 1) a
      ; else
      (loop (- n 1) (* n a)))))

; exponential series
(define series-exp
  (stream-map 
    (lambda (n) (/ 1 (fact n)))
    (integers-from 0)))

; s(x) approximated with num terms
(define (series-eval s x num)
  (if (= 0 num) 0
    ; else
    (+ (s 'car) (* x (series-eval (s 'cdr) x (- num 1))))))

; stack friendly, but not as nice
(define (series-eval2 s x num)
  (let loop ((s s) (num num) (sum 0) (z 1))
             (if (= 0 num) sum
               ; else
               (loop (s 'cdr) (- num 1) (+ sum (* (s 'car) z)) (* z x)))))



