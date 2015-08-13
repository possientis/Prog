(load "hash.scm")

(define (same-key? x y) (equal? x y))

(define (hash-test)
  ;;
  (define a (dictionary same-key?))
  (define b (dictionary equal?))
  ;;
  (display "hash: starting unit test\n")
  ;;
  ;; prehash: testing for two possible values under 'scm' or 'mit-scheme'
  (let ((u (prehash "hi")))
    (if (and (not (= 26984 u)) (not (= 1769415228 u)))
    (display "hash: unit testing 1 failing\n")))
  ;;
  ((a 'insert!) 1 10)
  ;;
  ;;
  (display "hash: unit test complete\n"))

(hash-test)
(quit)

