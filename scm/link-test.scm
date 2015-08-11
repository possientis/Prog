(load "link.scm")

(define (link-test)

  (define a (link (lambda (x y) (equal? x y))))
  (define b (link equal?))

  (display "link: starting unit test\n")
  ;; insert
  ((a 'insert!) 1 10)
  ((b 'insert!) 1 10)
  ((a 'insert!) 3 30)
  ((b 'insert!) 3 30)
  ((a 'insert!) 2 20)
  ((b 'insert!) 2 20)
  ((a 'insert!) 5 50)
  ((b 'insert!) 5 50)

  (a 'print)
  (newline)

  (display "link: unit test complete\n"))

(link-test)
(quit)
