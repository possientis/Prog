(load "queue.scm")

(define process-queue (queue))

(define (fork proc)
  (call-with-current-continuation
    (lambda (k)
      ((process-queue 'push!) k)
      (proc))))

(define (yield)
  (call-with-current-continuation
    (lambda (k)
      ((process-queue 'push!) k)
      ((process-queue 'read!) 0)a))); running continuation with argument, dunno why


(define (thread-exit)
  (if (process-queue 'isempty?)
    (exit 0)
    ((process-queue 'read!) 0)))



(define (do-stuff-n-print str)
  (lambda()
    (let loop ((n 0))
      (if (< n 5)
        (begin
          (display str)
          (display ":")
          (display n)
          (newline)
          (yield)
          (loop (+ n 1)))))))

; I don't understand the output, need to come back
(fork (do-stuff-n-print "This is AAA"))
(fork (do-stuff-n-print "This is BBB"))
(fork (do-stuff-n-print "This is CCC"))
(fork (do-stuff-n-print "This is DDD"))

(thread-exit)
