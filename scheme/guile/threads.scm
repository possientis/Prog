(define threads (all-threads))

(display "number of running threads: ")(display (length threads))(newline)

(display "list of threads: ")(display threads)(newline)

(define current (current-thread))

(display "current thread: ")(display current)(newline)

(if (eq? current (car threads))
  (display "the unique thread is the current thread\n"))

(display (thread? current))(newline)

(define new-thread
  (call-with-new-thread 
    (lambda() (display "number of running threads is now: ")
              (display (length (all-threads)))
              (newline)
              3)))  ; return value

(define x (join-thread new-thread))     ; waiting for new-thread to terminate
(display "new thread exited?: ")(display (thread-exited? new-thread))(newline)

(display "return value from new thread: ")(display x)(newline)
(display (thread? new-thread))(newline) ; #t , eventhough thread as terminated
(display "number of running threads: ")(display (length (all-threads)))(newline)

(define t1 (call-with-new-thread
             (lambda ()
               (yield)
               (display "thread1:A\n")
               (yield)
               (display "thread1:B\n")
               (yield)
               (display "thread1:C\n"))))

(define t2 (call-with-new-thread
             (lambda ()
               (display "thread2:A\n")
               (yield)
               (display "thread2:B\n")
               (yield)
               (display "thread2:C\n"))))

(define t3 (call-with-new-thread
             (lambda ()
               (display "thread3:A\n")
               (yield)
               (display "thread3:B\n")
               (yield)
               (display "thread3:C\n"))))


(join-thread t1)
(join-thread t2)
(join-thread t3)

(display "All threads have exited\n")




(exit 0)
