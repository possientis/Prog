;;; see thread-basic.scm for other (lower level) calls

;;; using higher level functions
(use-modules (ice-9 threads))

(define (waste time)
  (let loop ((i 0))
    (if (< i time)
      (loop (+ i 1)))))

(define (proc1 start)
  (let loop ((i start))
    (display "i = ")(display i)(newline)
    (loop (+ i 1))))


(define t1 (make-thread proc1 10))

(if (not (thread-exited? t1))
  (display "\nthread is stuck in infinite loop, stopping it...\n"))

(waste 10000)

(cancel-thread t1)

(join-thread t1)

(if (thread-exited? t1)
  (display "thread has now exited.\n"))





