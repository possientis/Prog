(let loop ((i 0))
  (if (< i 40000)
    (begin
      (loop (+ i 1)))))

(exit 0)
