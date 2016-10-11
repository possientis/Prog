(define (extgcd n m) ; returns some (u v) such that u.n + v.m = gcd(n,m)
  (let ((r (modulo n m))
        (q (quotient n m)))
    (cond ((= 0 r) (let((s (if (< m 0) -1 1)))
                     (list 1 (- s q))))
          (else (let ((l (extgcd m r)))
                  (list (cadr l) (- (car l) (* (cadr l) q))))))))

(define (inv n p) ; inverse of n modulo p
  (cond ((not (= 1 (gcd n p))) 'error) ; not invertible unless gcd(n,p)=1
        (else (mod (car (extgcd n p)) p))))
(define (mul x y p) ; multiplication mod p
  (mod (* x y) p))
