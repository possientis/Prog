;#!/usr/bin/scm
(load "bus.scm")

(define (bus-test)

  (define a (bus 12))
  (define b (bus 8))
  (define x (bus 16))
  (define y (bus 16))
  (define s (bus 16))
  (define cin (wire))
  (define cout (wire))

  ;; start
  (display "bus: starting unit test\n")
  (if (not (= 12 (a 'size))) (display "bus: unit test 1 failing\n"))
  (if (not (= 8 (b 'size))) (display "bus: unit test 2 failing\n"))
  ;; testing set-signal! and get-signal
  ;; testing bus a
  (let ((N (expt 2 (a 'size)))) ;; highest unsigned integer on bus + 1
    (let loop ((i 0))
      (if (< i N)
        (begin
          ((a 'set-signal!) i)
          (if (not (= i (a 'get-signal)))
            (begin
              (display "bus: unit test 3 failing for integer ")
              (display i)
              (newline)))
          (loop (+ i 1))))))
  ;; testing bus b
  (let ((N (expt 2 (b 'size)))) ;; highest unsigned integer on bus + 1
    (let loop ((i 0))
      (if (< i N)
        (begin
          ((b 'set-signal!) i)
          (if (not (= i (b 'get-signal)))
            (begin
              (display "bus: unit test 4 failing for integer ")
              (display i)
              (newline)))
          (loop (+ i 1))))))
  ;; testing get-wire
  ((a 'set-signal!) (- (expt 2 (a 'size)) 1))  ; all bits set to 1
  (let loop ((i 0))
    (if (< i (a 'size))
      (begin
        (let ((signal (((a 'get-wire) i) 'get-signal))) ;ith bit = signal
          (if (not (eq? #t signal))
            (begin
              (display "bus: unit test 5 failing for bit ")
              (display i)
              (newline))))
        (loop (+ i 1)))))
  ((a 'set-signal!) 0)  ; all bits sets to 0
  (let loop ((i 0))
    (if (< i (a 'size))
      (begin
        (let ((signal (((a 'get-wire) i) 'get-signal))) ;ith bit = signal
          (if (not (eq? #f signal))
            (begin
              (display "bus: unit test 6 failing for bit ")
              (display i)
              (newline))))
        (loop (+ i 1)))))

  ;; testing ripple adder
  (ripple-adder x y cin s cout)
  (let ((N 64))
    (let loopX ((i 0))
      (if (< i N)
        (begin
          (let loopY ((j 0))
            (if (< j N)
              (begin
                ((cin 'set-signal!) #f) ; ensures input carry is off
                ((x 'set-signal!) i)
                ((y 'set-signal!) j)
                (schedule 'propagate!)  ; computes i + j -> bus s
                (if (not (= (+ i j) (s 'get-signal)))
                  (display "bus: unit test 7 failing\n"))
                (if (not (eq? #f (cout 'get-signal)))
                  (display "bus: unit test 8 failing\n"))
                ((cin 'set-signal!) #t) ; ensures input carry is on
                (schedule 'propagate!)  ; computes i + j + 1 -> bus s
                (if (not (= (+ i j 1) (s 'get-signal)))
                  (display "bus: unit test 9 failing\n"))
                (if (not (eq? #f (cout 'get-signal)))
                  (display "bus: unit test 10 failing\n"))
                (loopY (+ j 1)))))
          (loopX (+ i 1))))))
  ;; end
  (display "bus: unit test complete"))

(bus-test)
(quit)
