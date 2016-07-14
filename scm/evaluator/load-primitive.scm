;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-load-primitive)) 
  (begin
    (define included-load-primitive #f)  ; include guard
    (display "loading load-primitive")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (load-primitive file-name)
  (let ((file (open-file file-name "r")))
    (define (loop)
      (let ((input (read file)))
        (if (not (eof-object? input))
          (begin
            (eval input global-env)
            (loop)))))
    (loop)
    (close-port file))
  (string-append " " file-name " loaded"))


))  ; include guard
