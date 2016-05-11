(if (not (defined? included-load-file)) 
  (begin
    (define included-load-file #f)  ; include guard
    (display "loading load-file")(newline)


(define (load-file file-name)
  (let ((file (open-file file-name "r")))
    (define (loop)
      (let ((input (read file)))
        (if (not (eof-object? input))
          (begin
;            (newline) (display "input = ")(display input)(newline)
            (eval input global-env)
            (loop)))))
    (loop)
    (close-port file))
  (string-append " " file-name " loaded"))


))  ; include guard
