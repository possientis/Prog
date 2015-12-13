(load "stream.scm")

; inefficient
(define (stream-sqrt2 x)
  (stream-cons
    1
    (stream-map
      (lambda (guess) (* 0.5 (+ guess (/ x guess))))
      (stream-sqrt2 x))))

; far more efficient
(define (stream-sqrt x)
  (letrec ((seq 
             (stream-cons
               1
              (stream-map
                (lambda (guess) (* 0.5 (+ guess (/ x guess))))
                seq))))
    seq))

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
  (stream-cons s (make-tableau transform (transform s))))

(define (accelerate transform s)
  (stream-map (lambda (s) (s 'car))
              (make-tableau transform  s)))

(define pi-stream3
  (accelerate euler-transform pi-stream))

(define (stream-limit s tolerance)
  (let loop ((s s))
    (if (< (abs (- (s 'car) ((s 'cdr) 'car))) tolerance)
      ((s 'cdr) 'car)
      (loop (s 'cdr)))))

(define (stream-limit2 s tolerance)
  (if (< (abs (- (s 'car) ((s 'cdr) 'car))) tolerance)
    ((s 'cdr) 'car)
    (stream-limit2 (s 'cdr) tolerance)))

(define (sqrt2 x tolerance)
  (stream-limit (stream-sqrt x) tolerance))

(define (ln2-summands n)
  (stream-cons 
    (/ 1 n)
    (stream-map - (ln2-summands (+ n 1)))))

(define ln2-stream
  (stream-partial-sums (ln2-summands 1)))

(define ln2-stream2
  (euler-transform ln2-stream))

(define ln2-stream3
  (accelerate euler-transform ln2-stream))



