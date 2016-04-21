; exponentiation
; fast and stack friendly but no modulo 
(define (^ a n)
  (let loop ((a a) (n n) (prod 1))
    (cond ((= n 0) prod)
          ((even? n) (loop (* a a) (/ n 2) prod))
          ((odd? n) (loop a (- n 1) (* a prod)))
          (else (display "^: unexpected argument\n")))))

; elliptic curve over Fp where:
(define p 
  115792089237316195423570985008687907853269984665640564039457584007908834671663)

; equation 
; y^2 mod p = (x^3 + 7) mod p


(define x 
  55066263022277343669578718895168534326250603453777594175500187360389116729240)

(define y 
  32670510020758816978083085130507043184471273380659243275938904335757337482424)

; checking that (x,y) is a point of secp256k1
(define a (+ 7 (^ x 3)))
(define b (^ y 2))
(define c (- a b))
(define d (modulo c p))
(if (not (= 0 d)) (error "(x,y) is not a point of secp256k1"))

; checking p = 2^256 - 0X1000003D1
(define q1 (^ 2 256))
(define q2 (- q1 (^ 2 32)))
(define q3 (- q2 (^ 2 9)))
(define q4 (- q3 (^ 2 8)))
(define q5 (- q4 (^ 2 7)))
(define q6 (- q5 (^ 2 6)))
(define q7 (- q6 16))
(define q (- q7 1))
(if (not (= q p)) (error "prime humber p is unexpected"))




