(define (parallel-execute p1 p2)
 (let ((ready-flag #f))
    (define (busy-wait)
      (if (eq? #f ready-flag) (busy-wait)))
    (let ((pid1 (fork)))
      (if (= 0 pid1)  ; child process
        (begin
          (busy-wait) ; busy-wait for signal from parent process
          (display "running p1\n")
          (p1))
        (begin        ; parent process
          (let ((pid2 (fork)))
            (if (= 0 pid2)  ; child process
              (begin
                (busy-wait)
                (display "running p2\n")
                (p2)))
            (begin    ; parent process
              (set! ready-flag #t)  ; this will not be seen by children !!!
              (let loop ((i 1000000))
                (if (> i 0)
                  (begin
                    ; do nothing
                    (loop (- i 1)))))
              (kill pid1 1)
              (kill pid2 1))))))))

(define (f) (display "I am running\n"))

