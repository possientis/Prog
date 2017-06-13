(use-modules (ice-9 threads))

(define mutex (make-mutex))
(define mutex2 (make-mutex 'recursive))
(define mutex3 (make-recursive-mutex))

(display (mutex? mutex))(newline)
(display (mutex? mutex2))(newline)
(display (mutex? mutex3))(newline)


(define (waste time)
  (let loop ((i 0))
    (if (< i time)
      (loop (+ i 1)))))

(define (proc args)
  (let ((num (car args))
        (mutex (cadr args)))
    (let loop ((i 0))
      (display "thread n. ")
      (display num)
      (display ": i = ")
      (display i)
      (newline)
      (loop (+ i 1)))))


(define t1 (make-thread proc (list 1 mutex)))
(define t2 (make-thread proc (list 2 mutex)))
(define t3 (make-thread proc (list 3 mutex)))

(waste 100000)

(cancel-thread t1)
(cancel-thread t2)
(cancel-thread t3)

(join-thread t1)
(join-thread t2)
(join-thread t3)

(display "All threads have been terminated.\n")

