(load "dict.scm")

(define (same-key? x y) (equal? x y))

(define (hash-test)
  ;;
  (define a (dictionary same-key?))
  (define b (dictionary equal?))
  ;;
  (display "hash: starting unit test\n")
  ;;
  ;; prehash: testing for two possible values under 'scm' or 'mit-scheme'
  (let ((u ((a 'prehash) "hi")))
    (if (and (not (= 26984 u)) (not (= 1769415228 u)))
    (display "hash: unit testing 1 failing\n")))
  ;; first insert
  ((a 'insert!) 1 10)
  ((b 'insert!) "abc" 100)
  (if (not (a 'check)) (display "hash: unit test 1.1 failing\n"))
  (if (not (b 'check)) (display "hash: unit test 1.2 failing\n"))
  ;; should fail
  (if (not (eq? #f ((a 'find) 0))) (display "hash: unit test 1 failing\n"))
  (if (not (eq? #f ((b 'find) "abd"))) (display "hash: unit test 2 failing\n"))
  ;; should succeed
  (let ((x ((a 'find) 1)))
    (if (eq? #f x) (display "hash: unit test 3 failing\n"))
    (if (not (same-key? 1 (car x))) (display "hash: unit test 4 failing\n"))
    (if (not (= 10 (cdr x))) (display "hash: unit test 5 failing\n")))
  (let ((x ((b 'find) "abc")))
    (if (eq? #f x) (display "hash: unit test 6 failing\n"))
    (if (not (equal? "abc"  (car x))) (display "hash: unit test 7 failing\n"))
    (if (not (= 100 (cdr x))) (display "hash: unit test 8 failing\n")))
  ;; second insert
  ((a 'insert!) 2 20)
  ((b 'insert!) "def" 200)
  (if (not (a 'check)) (display "hash: unit test 8.1 failing\n"))
  (if (not (b 'check)) (display "hash: unit test 8.2 failing\n"))
  ;; should fail
  (if (not (eq? #f ((a 'find) 0))) (display "hash: unit test 9 failing\n"))
  (if (not (eq? #f ((b 'find) "abd"))) (display "hash: unit test 10 failing\n"))
  ;; should succeed
  (let ((x ((a 'find) 1)))
    (if (eq? #f x) (display "hash: unit test 11 failing\n"))
    (if (not (same-key? 1 (car x))) (display "hash: unit test 12 failing\n"))
    (if (not (= 10 (cdr x))) (display "hash: unit test 13 failing\n")))
  (let ((x ((b 'find) "abc")))
    (if (eq? #f x) (display "hash: unit test 14 failing\n"))
    (if (not (equal? "abc"  (car x))) (display "hash: unit test 15 failing\n"))
    (if (not (= 100 (cdr x))) (display "hash: unit test 16 failing\n")))
  (let ((x ((a 'find) 2)))
    (if (eq? #f x) (display "hash: unit test 17 failing\n"))
    (if (not (same-key? 2 (car x))) (display "hash: unit test 18 failing\n"))
    (if (not (= 20 (cdr x))) (display "hash: unit test 19 failing\n")))
  (let ((x ((b 'find) "def")))
    (if (eq? #f x) (display "hash: unit test 20 failing\n"))
    (if (not (equal? "def"  (car x))) (display "hash: unit test 21 failing\n"))
    (if (not (= 200 (cdr x))) (display "hash: unit test 22 failing\n")))
  ;; delete
  ((a 'delete!) 3)
  ((a 'delete!) 2)
  ((a 'delete!) 1)
  ((a 'delete!) 4)
  ((b 'insert!) "ghi" 300)

  (a 'debug)
  (b 'debug)
  ;;
  (display "hash: unit test complete\n"))

(hash-test)
(quit)

