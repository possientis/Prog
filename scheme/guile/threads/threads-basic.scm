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

;;; thread will loop for ever
(define t1 (call-with-new-thread
             (lambda ()
               (let loop ((i 0))
                 (display "i = ")(display i)(newline)
                 (loop (+ 1 i))))))

(if (not (thread-exited? t1))
  (display "thread t1 is currently stuck in an infinite loop...\n"))

(display "setting up thread t1's clean up procedure...\n")

(set-thread-cleanup! t1 (lambda () (display "\nOk ok, I am exiting now...\n")))


(let loop ((i 0))
  (if (< i 10000)
    (loop (+ i 1))))

(display "\ncancelling thread t1 now...\n")

(cancel-thread t1)

(join-thread t1)

(if (thread-exited? t1)
  (display "thread t1 has now exited...\n"))

(display "All threads have exited\n")




(exit 0)
