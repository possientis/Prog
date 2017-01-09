(load "number.scm")
(load "rand.scm")
(load "test-abstract.scm")
(load "test-number.scm")

(define x (number 'from-integer 25))
(define y (number 'from-integer 3))
(define w (number 'from-integer -12))

(define zero (number 'zero))
(define one (number 'one))

(display "zero = ")(display (zero 'to-string))(newline)
(display "one = ")(display (one 'to-string))(newline)
(display "x = ")(display (x 'to-string))(newline)
(display "y = ")(display (y 'to-string))(newline)

(define z (x 'add y))
(define t (x 'mul y))

(display "x + y = ")(display (z 'to-string))(newline)
(display "x * y = ")(display (t 'to-string))(newline)

(display "-x = ")(display ((x 'negate) 'to-string))(newline)

(display "x<y : ")(display (x 'compare-to y))(newline)
(display "y<x : ")(display (y 'compare-to x))(newline)
(display "x<x : ")(display (x 'compare-to x))(newline)

(display "(x 'hash) = ")(display (x 'hash))(newline)
(display "(y 'hash) = ")(display (y 'hash))(newline)
;
(display "(x 'sign) = ")(display (x 'sign))(newline)
(display "(zero 'sign) = ")(display (zero 'sign))(newline)
(display "(w 'sign) = ")(display (w 'sign))(newline)

(display "(x 'to-bytes 32) = ")(display (x 'to-bytes 32))(newline)

(display "(bit-length zero) = ")(display (zero 'bit-length))(newline)
(display "(bit-length one) = ")(display (one 'bit-length))(newline)
(display "(bit-length -one) = ")(display ((one 'negate) 'bit-length))(newline)
(display "(bit-length x) = ")(display (x 'bit-length))(newline)
(display "(bit-length y) = ")(display (y 'bit-length))(newline)

(let ((bytes (x 'to-bytes 32)))
  (let ((xx (number 'from-bytes 1 bytes))
        (yy (number 'from-bytes -1 bytes)))
    (display "xx = ")(display (xx 'to-string))(newline)
    (display "yy = ")(display (yy 'to-string))(newline)))

(define gen (rand 'new))

(define bytes (gen 'get-random-bytes 32))

(define test (number 'from-bytes 1 bytes))

(display "test = ")(display (number->string (test 'to-integer) 16))(newline)

(display (number->string (bit-field #b1101101010 0 6) 2))(newline)

(display (ash 9 -1))(newline)

(define r (number 'random 256))

(display "r = ")(display (r 'to-string))(newline)

(define r0 (number 'random 0))
(display "r0 = ")(display (r0 'to-string))(newline)

(define r1 (number 'random 1))
(display "r1 = ")(display (r1 'to-string))(newline)

(define r2 (number 'random 2))
(display "r2 = ")(display (r2 'to-string))(newline)

(define gen2 (test-abstract 'generator))

(define r3 (number 'from-bytes 1 (gen2 'get-random-bytes 32)))
(display "r3 = ")(display (r3 'to-string))(newline)

(define test1 (test-abstract 'new #f))

(display (test1 'self))(newline)

(define r4 (number 'from-bytes 1 (get-random-bytes 32)))
(display "r4 = ")(display (r4 'to-string))(newline)

;(test1 'run)

(log-message "This is an error message")

(check-equals "abc" "abc" "testing check-equals")

(check-condition #t "testing check-condition")

(define test2 (test-number))

(test2 'run)


(exit 0)
