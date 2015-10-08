(define (busy-wait)
  (let loop ((i 1000000))
    (if (> i 0)
      (loop (- i 1)))))

(define x 10)

(define (parallel-execute p1 p2)
  (let ((pid1 (fork)))
    (if (= 0 pid1)  ; child process
      (begin
        (busy-wait) ; gives time to other process to get ready
        (display "running p1\n")
        (p1)
        (exit 0))
      (begin        ; parent process
        (let ((pid2 (fork)))
          (if (= 0 pid2)  ; child process
            (begin
              (busy-wait) ; gives time to other process to finish busy wait
              (display "running p2\n")
              (p2)
              (exit 0))
            (begin    ; parent process
              (waitpid pid1 0)
              (waitpid pid2 0)
              (display "parent process terminating\n"))))))))

(define (f) (display "I am running\n"))

(parallel-execute f f)

