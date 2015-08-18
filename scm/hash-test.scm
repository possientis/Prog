(load "hash.scm")

(define (hash-test)
  ;;
  (display "hash: starting unit test\n")
  ;;
  ;; prehash: testing for two possible values under 'scm' or 'mit-scheme'
  (let ((u (((hash-lib) 'prehash) "hi")))
    (if (and (not (= 26984 u)) (not (= 1769415228 u)))
    (display "hash: unit testing 1 failing\n")))

  (display "hash: unit test complete\n"))

(hash-test)
(quit)

