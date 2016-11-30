(load "queue.scm")

(define (queue-test)
  ;; defining a few queues for testing
  (define a (queue))
  (define b (queue))
  (define list-a '("hello" #\a 'foo))
  ;;
  (display "queue: starting unit test\n")
  ;; checking initial state
  (if (not (a 'isempty?)) (display "queue: unit-test 1 failing\n"))
  (if (not (b 'isempty?)) (display "queue: unit-test 2 failing\n"))
  ;; adding one element to queue
  ((a 'push!) '(1 2))
  ((b 'push!) 3)
  (if (a 'isempty?) (display "queue: unit-test 5 failing\n"))
  (if (b 'isempty?) (display "queue: unit-test 6 failing\n"))
  ;; adding a second element to queue
  ((a 'push!) '("hello" #\a 'foo))
  ((b 'push!) 'bar)
  (if (a 'isempty?) (display "queue: unit-test 9 failing\n"))
  (if (b 'isempty?) (display "queue: unit-test 10 failing\n"))
  ;; adding a third element to queue
  ((a 'push!) 5)
  ((b 'push!) '(7 8))
  (if (a 'isempty?) (display "queue: unit-test 9 failing\n"))
  (if (b 'isempty?) (display "queue: unit-test 10 failing\n"))
  ;; reading first element from queue
  (if (not (equal? (a 'read!) '(1 2))) (display "queue: unit-test 11 failing\n"))
  (if (not (equal? (b 'read!) 3)) (display "queue: unit-test 12 failing\n"))
  (if (a 'isempty?) (display "queue: unit-test 13 failing\n"))
  (if (b 'isempty?) (display "queue: unit-test 14 failing\n"))
  ;; reading second element from queue
  (if (not (equal? (a 'read!) list-a)) (display "queue: unit-test 15 failing\n"))
  (if (not (equal? (b 'read!) 'bar)) (display "queue: unit-test 16 failing\n"))
  (if (a 'isempty?) (display "queue: unit-test 17 failing\n"))
  (if (b 'isempty?) (display "queue: unit-test 18 failing\n"))
  ;; reading last  element from queue
  (if (not (equal? (a 'read!) 5)) (display "queue: unit-test 19 failing\n"))
  (if (not (equal? (b 'read!) '(7 8))) (display "queue: unit-test 20 failing\n"))
  (if (not (a 'isempty?)) (display "queue: unit-test 21 failing\n"))
  (if (not (b 'isempty?)) (display "queue: unit-test 22 failing\n"))
  ;; exiting
  (display "queue: unit test complete\n")
  'done)

(queue-test)
(exit 0)
