(define p
  115792089237316195423570985008687907853269984665640564039457584007908834671663)
(define q (- p 1))


;; worse case sqrt O(sqrt(n))
(define (prime? n)
(define (smallest-divisor n)
  (define (divide? x y)
    (= 0 (modulo y x)))
  (define (square x)
    (* x x))  ; undefined for scm
  (let loop ((n n) (div 2))
    (cond ((> (square div) n) n)
          ((divide? div n) div)
          (else (loop n (+ 1 div))))))
(and (< 1 n) (= n (smallest-divisor n))))


(define (expmod a n m)    ; a^n mod m
  (let loop ((a a) (n n) (m m ) (prod 1))
    (cond ((= 0 n) (modulo prod m))
          ((even? n) (loop (modulo (* a a) m) (/ n 2) m prod))
          ((odd? n) (loop a (- n 1) m (modulo (* prod a) m)))
          (else (display "unexpected error\n")))))

;; testing whether (test-value)^(n-1) = 1 mod n
;; which should be the case when n is prime and
;; test-value is not divisible by n (Fermat)
(define (pseudo-prime1? n test-value)
  (= 1 (expmod test-value (- n 1) n)))

;; testing whether (test-value)^n = test-value mod n
;; which should be the case when n is prime
;; Note that a^n = a mod n does not imply that
;; a^(n-1) = 1 mod n, a is invertible mod n
;; (which is the case when a /\ n = 1)

(define (pseudo-prime2? n test-value)
  (= (modulo test-value n) (expmod test-value n n)))

(define (carmichael? n)
  ;; returns #t of numbers greater than 1 which are not
  ;; prime and yet for which a^n = a mod n for all a
  (let loop ((x 1))
    (cond ((= x n) (and (not (prime? n)) (< 1 n)))
          ((pseudo-prime2? n x) (loop (+ 1 x)))
          (else #f))))

;; This function will always return #f
;; as strong-carmichael => prime
(define (strong-carmichael? n)
  ;; returns #t of numbers greater than 1 which are not
  ;; prime and yet for which a^(n-1) = 1 mod n for all a
  ;; which are not divisible by n, hence for all a
  ;; between 1 and (n-1) inclusive.
  (let loop ((x 1))
    (cond ((= x n) (and (not (prime? n)) (< 1 n)))
          ((pseudo-prime1? n x) (loop (+ 1 x)))
          (else (display x) (display " as test value lead to pseudo-primality test failure\n") #f))))

(define (search-carmichael n)
  (let loop ((x 2))
    (cond ((= x n) 'done)   ; search for all carmichael numbers < n
          (else (if (carmichael? x)(begin (display x) (display " ")))
                (loop (+ 1 x))))))

;; pseudo-prime1? is a lot harder to be fooled
;; yet it may report a number as prime wrongly

(define (search-false-positive n)
  (let loop ((x 6))
    (if (<= n x)
      'done
      (begin
        (if (and (pseudo-prime1? x 2)
                 (pseudo-prime1? x 3)
                 (pseudo-prime1? x 5)
                 (pseudo-prime1? x 7)
                 (pseudo-prime1? x 11)
                 (pseudo-prime1? x 13)
                 (pseudo-prime1? x 17)
                 (pseudo-prime1? x 19)
                 (pseudo-prime1? x 23)
                 (pseudo-prime1? x (- x 1))
                 (not (prime? x)))
          (begin (display x) (display " ")))
        (loop (+ 1 x))))))






