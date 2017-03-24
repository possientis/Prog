(define lazy?
  (let ((**lazy?** #t))
    (let ((unset-lazy (lambda () (set! **lazy?** #f)))
          (try (lambda (x) 'done)))
      (lambda () (try (unset-lazy)) **lazy?**))))


(display "lazy? = ")(display (lazy?))(newline)

(exit 0)

