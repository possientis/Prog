(use-modules (ice-9 threads))

(define stdout-mutex (make-mutex))


(define turn 1)                   ; shared mutable state
(define turn-mutex (make-mutex))  ; needed to protect shared mutable state

(define (next)
  (lock-mutex turn-mutex)
  (if (= turn 3)
    (set! turn 1)
    (set! turn (+ 1 turn)))
  (unlock-mutex turn-mutex))

(define (read-turn)
  (lock-mutex turn-mutex)
  (let ((t turn))
    (unlock-mutex turn-mutex)
    t))

(define (waste time)
  (let loop ((i 0))
    (if (< i time)
      (loop (+ i 1)))))

(define (report num i)
  (lock-mutex stdout-mutex)      ; blocks until mutex acquired
  (display "thread n. ")
  (display num)
  (display ": i = ")
  (display i)
  (newline)
  (unlock-mutex stdout-mutex))
 
(define proceed-mutex (make-mutex))

(define (proc args)
  (let ((num (car args)))
    (let loop ((i 0))
      (lock-mutex proceed-mutex)
      (report num i)
      (next)
      (unlock-mutex proceed-mutex)
      (yield)
      (loop (+ i 1)))))


(define t1 (make-thread proc (list 1)))
(define t2 (make-thread proc (list 2)))
(define t3 (make-thread proc (list 3)))

(waste 100000)

(cancel-thread t1)
(cancel-thread t2)
(cancel-thread t3)

(join-thread t1)
(join-thread t2)
(join-thread t3)

(display "\nAll threads have been terminated.\n")

