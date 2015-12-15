#!/usr/bin/scm
(load "stream.scm")

(define (stream-test)
  ;
  (define ones (stream-cons 1 ones))
  (define (sieve s)
    (stream-cons 
      (s 'car)
      (sieve (stream-filter
               (lambda (x) (not (= 0 (modulo x (s 'car)))))
               (s 'cdr)))))
  ;
  ; a first possible definition of the fibonacci stream
  (define fibs1
  (let fibgen ((a 0) (b 1))
    (stream-cons a (fibgen b (+ a b)))))
  ; a second possible definition of the fibonacci stream
  (define fibs2 (stream-cons 0 (stream-cons 1 (stream-map + fibs2 (fibs2 'cdr)))))

  (display "stream: starting unit test\n")
  ; empty stream
  (let ((s (stream)))
    (if (not (s 'null?)) (display "stream: unit test 1.0 failing\n"))
    (if (not (equal? (stream->list s) '()))
      (display "stream: unit test 1.1 failing\n"))
    (if (not (equal? (stream-take 10 s) '()))
      (display "stream: unit test 1.2 failing\n"))
    (if (not ((list->stream '()) 'null?))
      (display "stream: unit test 1.3 failing\n")))
  ; one elment stream
  (let ((s (stream-cons 5 (stream)))) ; s = (5)
    ; stream should not be empty
    (if (s 'null?) (display "stream: unit test 2.0 failing\n"))
    ; checking car
    (if (not (= 5 (s 'car))) (display "stream: unit test 2.1 failing\n"))
    (if (not ((s 'cdr) 'null?)) (display "stream: unit test 2.2 failing\n"))
    (if (not (= 5 (stream-ref s 0))) (display "stream: unit test 2.3 failing\n"))
    (if (not (equal? (stream->list s) '(5)))
      (display "stream: unit test 2.4 failing\n"))
    (if (not (equal? (stream-take 1 s) '(5)))
      (display "stream: unit test 2.5 failing\n")))
  ; two element stream
  (let ((s (list->stream '(5 7))))
    (if (s 'null?) (display "stream: unit test 3.0 failing\n"))
    (if (not (= 5 (stream-ref s 0))) (display "stream: unit test 3.1 failing\n"))
    (if (not (= 7 (stream-ref s 1))) (display "stream: unit test 3.2 failing\n"))
    (if (not (equal? (stream->list s) '(5 7)))
      (display "stream: unit test 3.3 failing\n"))
    (if (not (equal? (stream-take 2 s) '(5 7)))
      (display "stream: unit test 3.4 failing\n")))
  ; more elements
  (let ((s (list->stream '(5 7 3 2 0 1 4 8))))
    (if (s 'null?) (display "stream: unit test 4.0 failing\n"))
    (if (not (= 5 (stream-ref s 0))) (display "stream: unit test 4.1 failing\n"))
    (if (not (= 7 (stream-ref s 1))) (display "stream: unit test 4.2 failing\n"))
    (if (not (= 3 (stream-ref s 2))) (display "stream: unit test 4.3 failing\n"))
    (if (not (= 2 (stream-ref s 3))) (display "stream: unit test 4.4 failing\n"))
    (if (not (= 0 (stream-ref s 4))) (display "stream: unit test 4.5 failing\n"))
    (if (not (= 1 (stream-ref s 5))) (display "stream: unit test 4.6 failing\n"))
    (if (not (= 4 (stream-ref s 6))) (display "stream: unit test 4.7 failing\n"))
    (if (not (= 8 (stream-ref s 7))) (display "stream: unit test 4.8 failing\n"))
    (if (not (equal? (stream->list s) '(5 7 3 2 0 1 4 8)))
      (display "stream: unit test 4.9 failing\n"))
    (if (not (equal? (stream-take 8 s) '(5 7 3 2 0 1 4 8)))
      (display "stream: unit test 4.10 failing\n")))
  ; some infinite streams (need recursive 'let' though, or will fail)
  (letrec ((s (stream-cons 1 s)))  ; s = (1 1 1 1 1 1 1 1 1 1 .....
    (if (s 'null?) (display "stream: unit test 5.0 failing\n"))
    (if (not (= 1 (stream-ref s 0))) (display "stream: unit test 5.1 failing\n"))
    (if (not (= 1 (stream-ref s 1))) (display "stream: unit test 5.2 failing\n"))
    (if (not (= 1 (stream-ref s 2))) (display "stream: unit test 5.3 failing\n"))
    (if (not (= 1 (stream-ref s 3))) (display "stream: unit test 5.4 failing\n"))
    (if (not (= 1 (stream-ref s 4))) (display "stream: unit test 5.5 failing\n"))
    (if (not (= 1 (stream-ref s 5))) (display "stream: unit test 5.6 failing\n"))
    (if (not (= 1 (stream-ref s 6))) (display "stream: unit test 5.7 failing\n"))
    (if (not (= 1 (stream-ref s 7))) (display "stream: unit test 5.8 failing\n"))
    (if (not (equal? (stream-take 8 s) '(1 1 1 1 1 1 1 1)))
      (display "stream: unit test 5.9 failing\n"))
    (if (not (equal? (stream-take 8 ones) '(1 1 1 1 1 1 1 1)))
      (display "stream: unit test 5.10 failing\n")))
  ; stream-for-each
  (let ((s (list->stream '(0 1 2 3 4 5)))
        (f (let ((count 0))
             (lambda (x)
               (set! count (+ count x))
               count))))
    (stream-for-each f s) ; internal 'count' should reach 15
    (if (not (= 15 (f 0))) (display "stream: unit test 7.0 failing\n")))
  ; integers-from
  (let ((s (integers-from 17)))
    (if (not (equal? (stream-take 8 s) '(17 18 19 20 21 22 23 24)))
      (display "stream: unit test 8.0 failing\n")))
  ; stream-filter
  (let ((s (integers-from 0)))
    (let ((s1 (stream-filter odd? s)) (s2 (stream-filter even? s)))
    (if (not (equal? (stream-take 8 s1) '(1 3 5 7 9 11 13 15)))
      (display "stream: unit test 9.0 failing\n"))
    (if (not (equal? (stream-take 8 s2) '(0 2 4 6 8 10 12 14)))
      (display "stream: unit test 9.1 failing\n"))))
  ; stream-map
  ; n = 0
  (let ((f (lambda (x) (* x x))))
    (let ((t (stream-map f)))
      (if (not (t 'null?)) (display "stream: unit test 10.0 failing\n"))))
  ; n = 1
  (let ((s (list->stream '(0 1 2 3 4 5))) (f (lambda (x) (* x x))))
    (let ((t (stream-map f s)))
      (if (not (equal? (stream->list t) '(0 1 4 9 16 25)))
        (display "stream: unit test 10.1 failing\n"))))
  (if (not ((stream-map (lambda (x) (* x x)) (stream)) 'null?))
    (display "stream: unit test 10.2 failing\n"))
  ; n = 2
  (let ((s1 (list->stream '(0 1 2 3 4 5)))
        (s2 (list->stream '(2 4 6 8 9 7))))
    (let ((t (stream-map + s1 s2)))
      (if (not (equal? (stream->list t) '(2 5 8 11 13 12)))
        (display "stream: unit test 10.3 failing\n"))))
  (let ((t (stream-map + ones ones)))
    (if (not (equal? (stream-take 10 t) '(2 2 2 2 2 2 2 2 2 2)))
      (display "stream: unit test 10.4 failing\n")))
  ; n = 3
  (let ((s1 (list->stream '(0 1 2 3 4 5)))
        (s2 (list->stream '(2 4 6 8 9 7)))
        (s3 (list->stream '(5 1 2 3 6 1))))
    (let ((t (stream-map + s1 s2 s3)))
      (if (not (equal? (stream->list t) '(7 6 10 14 19 13)))
        (display "stream: unit test 10.3 failing\n"))))
  ; fibonacci numbers
  (let ((seq (stream-take 10 fibs1)))
    (if (not (equal? seq '(0 1 1 2 3 5 8 13 21 34)))
      (display "stream: unit test 11.0 failing\n")))
  (let ((seq (stream-take 10 fibs2)))
    (if (not (equal? seq '(0 1 1 2 3 5 8 13 21 34)))
      (display "stream: unit test 11.1 failing\n")))
  ; primes
  (let ((primes (sieve (integers-from 2))))
    (let ((seq (stream-take 500 primes))) ; will fail for large numbers
      (let ((t (stream-take 10 primes)))
        (if (not (equal? t '(2 3 5 7 11 13 17 19 23 29)))
          (display "stream: unit test 12.0 failing\n")))))
  ; stream-scale
  (let ((s (list->stream '(0 1 2 3 4 5))))
    (let ((t (stream-scale s 2)))
      (if (not (equal? (stream->list t) '(0 2 4 6 8 10)))
        (display "stream: unit test 13.0 failing\n"))))
  ; double (need 'letrec' on this one)
  (letrec ((double (stream-cons 1 (stream-scale double 2))))
    (let ((t (stream-take 10 double)))
      (if (not (equal? t '(1 2 4 8 16 32 64 128 256 512)))
        (display "stream: unit test 14.0 failing\n"))))
  ; stream-add
  (let ((s1 (list->stream '(0 1 2 3 4 5)))
        (s2 (list->stream '(2 3 6 1 0 3))))
    (let ((t (stream-add s1 s2)))
      (if (not (equal? (stream->list t) '(2 4 8 4 4 8)))
        (display "stream: unit test 15.0 failing\n"))))
  (letrec ((s (stream-cons 1 (stream-add s s))))
    (let ((t (stream-take 10 s)))
      (if (not (equal? t '(1 2 4 8 16 32 64 128 256 512)))
        (display "stream: unit test 15.1 failing\n"))))
  ; stream-add
  (let ((s1 (list->stream '(0 1 2 3 4 5)))
        (s2 (list->stream '(2 3 6 1 0 3))))
    (let ((t (stream-mul s1 s2)))
      (if (not (equal? (stream->list t) '(0 3 12 3 0 15)))
        (display "stream: unit test 16.0 failing\n"))))
  (letrec ((factorials (stream-cons 1 (stream-mul factorials (integers-from 1)))))
    (let ((t (stream-take 6 factorials)))
      (if (not (equal? t '(1 1 2 6 24 120)))
        (display "stream: unit test 16.1 failing\n"))))
  ; stream-partial-sums
  (let ((s (list->stream '(2 0 4 5 2 9))))
    (let ((t (stream-partial-sums s)))
      (if (not (equal? (stream->list t) '(2 2 6 11 13 22)))
        (display "stream: unit test 17.0 failing\n"))))
  (let ((t (stream-partial-sums ones)))
    (if (not (equal? (stream-take 10 t) '(1 2 3 4 5 6 7 8 9 10)))
      (display "stream: unit test 17.1 failing\n")))
  ; steam-merge
  (let ((s1 (list->stream '(0 3 1 4 4 2 5 1)))
        (s2 (list->stream '(0 1 5 2 4 1 6 0))))
    (let ((t (stream-merge s1 s2)))
      (if (not (equal? (stream->list t) '(0 1 3 1 4 4 2 5 1 2 4 1 6 0)))
        (display "stream: unit test 18.0 failing\n"))))
  (letrec ((s  (stream-cons
                 1
                 (stream-merge 
                   (stream-merge
                     (stream-scale s 2)
                     (stream-scale s 3))
                   (stream-scale s 5)))))
    (if (not (equal? (stream-take 15 s) '(1 2 3 4 5 6 8 9 10 12 15 16 18 20 24)))
      (display "stream: unit test 18.1 failing\n")))
  ; stream-expand
  (let ((s (stream-expand 1 7 10))) ; 1/7 = 0.1428571428 (base 10)
    (if (not (equal? (stream-take 10 s) '(1 4 2 8 5 7 1 4 2 8)))
      (display "stream: unit test 19.0 failing\n")))
  (let ((s (stream-expand 1 3 2)))  ; 1/3 = 0.0101010101 (base 2)
    (if (not (equal? (stream-take 10 s) '(0 1 0 1 0 1 0 1 0 1)))
      (display "stream: unit test 19.1 failing\n")))
  ; stream-interleave
  (let ((s1 (stream-range 0 9))(s2 (stream-range 10 19)))
    (let ((s (stream-interleave s1 s2)))
      (if (not (equal? (stream->list s) 
                       '(0 10 1 11 2 12 3 13 4 14 5 15 6 16 7 17 8 18 9 19)))
        (display "stream: unit test 20.0 failing\n"))))
  ; stream-upper-pairs
  (let ((s1 (stream-range 0 3)) (s2 (stream-range 10 13)))
    (let ((s (stream-upper-pairs s1 s2)))
      (if (not (equal? 
                 (stream->list s)
                 '((0 10)(0 11)(1 11)(0 12)(1 12)(0 13)(2 12)(1 13)(2 13)(3 13))))
        (display "stream: unit test 21.0 failing\n"))))
  ; stream-pairs
  (let ((s1 (stream-range 0 2)) (s2 (stream-range 10 12)))
    (let ((s (stream-pairs s1 s2)))
      (if (not (equal? (stream->list s)
                       '((0 10)(0 11)(1 11)(1 10)(1 12)(0 12)(2 12)(2 10)(2 11))))
        (display "stream: unit test 22.0 failing\n"))))
  ;
  (display "stream: unit test complete\n"))



(stream-test)
(exit 0)
