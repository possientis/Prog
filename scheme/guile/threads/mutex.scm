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

(define (report num i)
  (lock-mutex mutex)      ; blocks until mutex acquired
  (display "thread n. ")
  (display num)
  (display ": i = ")
  (display i)
  (display ": myprogress = ")
  (display (my-progress num))
  (display ": progress = ")
  (display progress)
  (display ": max-progress = ")
  (display (max-progress))
  (newline)
  (unlock-mutex mutex))
 
(define progress (list 0 0 0))

(define (my-progress i)
  (cond ((eq? i 1) (car progress))
        ((eq? i 2) (cadr progress))
        ((eq? i 3) (caddr progress))
        (else error "my-progress: illegal index")))

(define (inc-progress i)
  (cond ((eq? i 1) (set-car! progress (+ 1 (car progress))))
        ((eq? i 2) (set-car! (cdr progress) (+ 1 (cadr progress))))
        ((eq? i 3) (set-car! (cddr progress) (+ 1 (caddr progress))))
        (else error "my-progress: illegal index")))


(define (max-progress)
  (apply max progress))


(define (proc args)
  (let ((num (car args)))
    (let loop ((i 0))
      (if (>= (my-progress num) (+ 1 (max-progress)))
        (begin 
          (yield)
          (loop i)))
      (report num i)
      (inc-progress num)
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

