#!/usr/bin/scm
(load "bus.scm")

(define (bus-test)

  (define a (bus 16))
  (define b (bus 8))

  ;; start
  (display "bus: starting unit test\n")
  ;; testing bus a
  (let ((N (expt 2 (a 'size)))) ;; highest unsigned integer on bus + 1
    (let loop ((i 0))
      (if (< i N)
        (begin
          ((a 'set-signal!) i)
          (if (not (= i (a 'get-signal)))
            (begin
              (display "bus: unit test 1 failing for integer ")
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
              (display "bus: unit test b failing for integer ")
              (display i)
              (newline)))
          (loop (+ i 1))))))

  ;; end
  (display "bus: unit test complete"))

(bus-test)
(quit)
