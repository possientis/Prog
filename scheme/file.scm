(define file (open-file "test.scm" open_read))

(define (loop)
  (let ((input (read file)))
    (if (eof-object? input)
      'ok
      (begin 
        (display input)(newline)
        (loop)))))

(loop)

(close-port file)
