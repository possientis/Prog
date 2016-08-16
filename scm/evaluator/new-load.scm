;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-load)) 
  (begin
    (define included-new-load #f)  ; include guard
    (display "loading new-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (new-load file-name)
  (let ((file (open-file file-name "r")))
    (define (loop)
      (let ((input (read file)))
        (if (not (eof-object? input))
          (begin
            (new-eval input)
            (loop)))))
    (loop)
    (close-port file))
  (string-append " " file-name " loaded"))


))  ; include guard
