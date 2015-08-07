(define (proc)
  (let loop ((i 0))
    (if (= i 10)
      (display "\n")
      (begin
        (display i)
        (display " ")
        (loop (+ 1 i))))))
