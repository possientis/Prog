#!/usr/bin/scm
(load "avl-node.scm")

(define (avl-node-test)

  (define a (avl-node 1 10))
  (define b (avl-node 2 20))
  (define c (avl-node 3 30))


  (display "avl-node: starting unit test\n")
  ;;
  ;; checking keys
  (if (not (= 1 (a 'key))) (display "avl-node: unit-test 1 failing\n"))
  (if (not (= 2 (b 'key))) (display "avl-node: unit-test 2 failing\n"))
  (if (not (= 3 (c 'key))) (display "avl-node: unit-test 3 failing\n"))
  ;;
  ;;checking values
  (if (not (= 10 (a 'value))) (display "avl-node: unit-test 4 failing\n"))
  (if (not (= 20 (b 'value))) (display "avl-node: unit-test 5 failing\n"))
  (if (not (= 30 (c 'value))) (display "avl-node: unit-test 6 failing\n"))
  ((a 'set-value!) 100)
  (if (not (= 100 (a 'value))) (display "avl-node: unit-test 7 failing\n"))
  ;;
  ;; checking left
  ((a 'set-left!) b)
  (if (not (eq? b (a 'left))) (display "avl-node: unit-test 8 failing\n"))
  ;; checking right
  ((a 'set-right!) c)
  (if (not (eq? c (a 'right))) (display "avl-node: unit-test 9 failing\n"))
  ;; checking parent
  ((b 'set-parent!) a)
  ((c 'set-parent!) a)
  (if (not (eq? a (b 'parent))) (display "avl-node: unit-test 10 failing\n"))
  (if (not (eq? a (c 'parent))) (display "avl-node: unit-test 11 failing\n"))
  ;; checking height
  (if (not (= -1 (a 'height))) (display "avl-node: unit-test 12 failing\n"))
  (if (not (= -1 (b 'height))) (display "avl-node: unit-test 13 failing\n"))
  (if (not (= -1 (c 'height))) (display "avl-node: unit-test 14 failing\n"))
  ((a 'set-height!) 1)
  ((b 'set-height!) 0)
  ((c 'set-height!) 0)
  (if (not (= 1 (a 'height))) (display "avl-node: unit-test 15 failing\n"))
  (if (not (= 0 (b 'height))) (display "avl-node: unit-test 16 failing\n"))
  (if (not (= 0 (c 'height))) (display "avl-node: unit-test 17 failing\n"))


  (display "avl-node: unit test complete\n"))

(avl-node-test)
(quit)
