;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-file-to-code)) 
  (begin
    (define included-file-to-code #f)  ; include guard
    (display "loading file-to-code")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (file->code file)
  (cons 'begin 
        (reverse 
          (let loop ((acc '()))
            (let ((input (read file)))
              (if (not (eof-object? input))
                (loop (cons input acc))
                acc))))))

(define (filename->code filename)
  (let ((file (open-file filename "r")))
    (let ((code (file->code file)))
      (close-port file)
      code)))

))  ; include guard

