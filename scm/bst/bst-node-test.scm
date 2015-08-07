(load "bst-node.scm")

(define (bst-node-test)

  (define a (bst-node 1 10))
  (define b (bst-node 2 20))
  (define c (bst-node 3 30))


  (display "bst-node: starting unit test\n")
  ;;
  ;; checking keys
  (if (not (= 1 (a 'key))) (display "bst-node: unit-test 1 failing\n"))
  (if (not (= 2 (b 'key))) (display "bst-node: unit-test 2 failing\n"))
  (if (not (= 3 (c 'key))) (display "bst-node: unit-test 3 failing\n"))
  ;;
  ;;checking values
  (if (not (= 10 (a 'value))) (display "bst-node: unit-test 4 failing\n"))
  (if (not (= 20 (b 'value))) (display "bst-node: unit-test 5 failing\n"))
  (if (not (= 30 (c 'value))) (display "bst-node: unit-test 6 failing\n"))
  ((a 'set-value!) 100)
  (if (not (= 100 (a 'value))) (display "bst-node: unit-test 7 failing\n"))
  ;;
  ;; checking left
  ((a 'set-left!) b)
  (if (not (eq? b (a 'left))) (display "bst-node: unit-test 8 failing\n"))
  ;; checking right
  ((a 'set-right!) c)
  (if (not (eq? c (a 'right))) (display "bst-node: unit-test 9 failing\n"))
  ;; checking parent
  ((b 'set-parent!) a)
  ((c 'set-parent!) a)
  (if (not (eq? a (b 'parent))) (display "bst-node: unit-test 10 failing\n"))
  (if (not (eq? a (c 'parent))) (display "bst-node: unit-test 11 failing\n"))


  (display "bst-node: unit test complete\n"))

(bst-node-test)
(quit)
