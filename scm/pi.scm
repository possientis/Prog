(load "stream.scm")

(define (stream-sqrt x)
  (stream-cons
    1
    (stream-map
      (lambda (guess) (* 0.5 (+ guess (/ x guess))))
      (stream-sqrt x))))


(define (pi-summands n)
  (stream-cons (/ 1.0 n)
               (stream-map - (pi-summands (+ n 2)))))

(define pi-stream
  (stream-scale (stream-partial-sums (pi-summands 1)) 4))

(define (square x) 
  (* x x))

(define (euler-transform s)
  (let ((s0 (stream-ref s 0))
        (s1 (stream-ref s 1))
        (s2 (stream-ref s 2)))
    (stream-cons
      (- s2 (/ (square (- s2 s1)) (+ s0 (* -2 s1) s2)))
      (euler-transform (s 'cdr)))))

(define pi-stream2
  (euler-transform pi-stream))

(define (make-tableau transform s)
  stream-cons s (make-tableau transform (transform s)))

(define (accelerate transform s)
  (stream-map (lambda (s) (s 'car))
              (make-tableau transform  s)))

;(define pi-stream3
;  (accelerate euler-transform pi-stream))

