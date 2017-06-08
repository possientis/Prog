(define arb (make-arbiter "arb1"))

(newline)
(display "first attempt at locking the arbiter:\n")
(define t1 (try-arbiter arb))
(if t1 
  (display "arbiter was unlocked and has now been locked.\n")
  (display "arbiter was already locked.\n"))

(newline)
(display "second attempt at locking the arbiter:\n")
(define t2 (try-arbiter arb))
(if t2 
  (display "arbiter was unlocked and has now been locked.\n")
  (display "arbiter was already locked.\n"))

(newline)
(display "first attempt at releasing the arbiter:\n")
(define t3 (release-arbiter arb))
(if t3
  (display "arbiter was locked and has now been released\n")
  (display "arbiter was already unlocked.\n"))

(newline)
(display "second attempt at releasing the arbiter:\n")
(define t4 (release-arbiter arb))
(if t4
  (display "arbiter was locked and has now been released\n")
  (display "arbiter was already unlocked.\n"))

(define pid (fork))
(if (eq? 0 pid) ; child process
  (display "child is running\n")
  (if (> pid 0)
    (display "parent process is running\n")
    (display "fork error\n")))


(exit 0)
