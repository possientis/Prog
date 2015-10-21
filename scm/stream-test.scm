#!/usr/bin/scm
(load "stream.scm")

(define (stream-test)
  ;
  ; defined with recursive let below, just checking define statement works
  (define ones (stream-cons 1 ones))

  (display "stream: starting unit test\n")
  ; empty stream
  (let ((s (stream)))
    (if (not (s 'null?)) (display "stream: unit test 1.0 failing\n"))
    (if (not (equal? (stream->list s) '()))
      (display "stream: unit test 1.1 failing\n"))
    (if (not (equal? (stream-take s 10) '()))
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
    (if (not (equal? (stream-take s 1) '(5)))
      (display "stream: unit test 2.5 failing\n")))
  ; two element stream
  (let ((s (list->stream '(5 7))))
    (if (s 'null?) (display "stream: unit test 3.0 failing\n"))
    (if (not (= 5 (stream-ref s 0))) (display "stream: unit test 3.1 failing\n"))
    (if (not (= 7 (stream-ref s 1))) (display "stream: unit test 3.2 failing\n"))
    (if (not (equal? (stream->list s) '(5 7)))
      (display "stream: unit test 3.3 failing\n"))
    (if (not (equal? (stream-take s 2) '(5 7)))
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
    (if (not (equal? (stream-take s 8) '(5 7 3 2 0 1 4 8)))
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
    (if (not (equal? (stream-take s 8) '(1 1 1 1 1 1 1 1)))
      (display "stream: unit test 5.9 failing\n"))
    (if (not (equal? (stream-take ones 8) '(1 1 1 1 1 1 1 1)))
      (display "stream: unit test 5.10 failing\n")))

  ;
  (display "stream: unit test complete\n"))

(stream-test)
(exit 0)
