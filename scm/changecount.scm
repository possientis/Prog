(define (d k)       ; array of coin denominations
  (cond ((= k 0) 1)
        ((= k 1) 5)
        ((= k 2) 10)
        ((= k 3) 25)
        ((= k 4) 50)
        (else (display "Out of bound error\n"))))

(define (DP n x)    ; ways of changing x using first n coins
  (if (= 0 n)
    (if (= 0 x) 1 0); (DP 0 0) = 1 and (DP 0 x) = 0 for x <> 0
    (if (< x 0)
      0             ; (DP n x) = 0 for x < 0
      ;; n > 0 and x >= 0 at this stage
      (+ (DP (- n 1) x) (DP n (- x (d (- n 1))))))))
