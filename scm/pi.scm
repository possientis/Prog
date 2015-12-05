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
