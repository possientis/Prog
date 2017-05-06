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
      ;
      ; Normally, this code runs in native scheme which carries out a 
      ; strict evaluation. However, it may be that we want to run this 
      ; code in our own interpreter which may happen to be lazy. In other 
      ; words, this code could end up being the argument of lazy-eval...
      ;
      ; When this happens, the variable 'code' is an unevaluated thunk
      ; and it is important that we force it in order to ensure the IO 
      ; operation on the port is carried out before we close the port.

      (force-thunk code)  ; has no effect if code is not a thunk    

      (close-port file)   ; IO needs to occur before this point

      code)))

))  ; include guard

