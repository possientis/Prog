(define (load-file file-name)
  (let ((file (open-file file-name open_read)))
    (define (loop)
      (let ((input (read file)))
        (if (not (eof-object? input))
          (begin
            (eval input global-env)
            (loop)))))
    (loop)
    (close-port file))
  (string-append " " file-name " loaded"))

