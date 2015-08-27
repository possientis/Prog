#!/usr/bin/scm
(load "link-node.scm")

(define (link-node-test)

  (define a (link-node 1 10))
  (define b (link-node 2 20))
  (define c (link-node 3 30))


  (display "link-node: starting unit test\n")
  ;;
  ;; checking keys
  (if (not (= 1 (a 'key))) (display "link-node: unit-test 1 failing\n"))
  (if (not (= 2 (b 'key))) (display "link-node: unit-test 2 failing\n"))
  (if (not (= 3 (c 'key))) (display "link-node: unit-test 3 failing\n"))
  ;;
  ;;checking values
  (if (not (= 10 (a 'value))) (display "link-node: unit-test 4 failing\n"))
  (if (not (= 20 (b 'value))) (display "link-node: unit-test 5 failing\n"))
  (if (not (= 30 (c 'value))) (display "link-node: unit-test 6 failing\n"))
  ((a 'set-value!) 100)
  (if (not (= 100 (a 'value))) (display "link-node: unit-test 7 failing\n"))
  ;;
  ;; next
  (if (not (null? (a 'next))) (display "link-node: unit-test 8 failing\n"))
  (if (not (null? (b 'next))) (display "link-node: unit-test 9 failing\n"))
  (if (not (null? (c 'next))) (display "link-node: unit-test 10 failing\n"))
  ;;
  ;; set-next!
  ((a 'set-next!) b)
  ((b 'set-next!) c)
  ((c 'set-next!) a)
  (if (not (eq? b (a 'next))) (display "link-node: unit-test 11 failing\n"))
  (if (not (eq? c (b 'next))) (display "link-node: unit-test 12 failing\n"))
  (if (not (eq? a (c 'next))) (display "link-node: unit-test 13 failing\n"))
  ;;
  (display "link-node: unit test complete\n"))

(link-node-test)
(quit)
