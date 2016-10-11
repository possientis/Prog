(define (read-port p)
  (define (loop ls)
    (let ((c (read-char p)))
      (if (eof-object? c)
        ls
        (loop (cons c ls)))))
 (list->string (reverse (loop '()))))


(define (read-file f)
  (let ((p (open-input-file f)))
    (let ((ls (read-port p)))
      (close-input-port p)
      ls)))

(define (read-file2 f)
  (call-with-input-file f (lambda (p)
                            (let ((ls (read-port p)))
                              (close-input-port p)
                              ls))))


(define s (read-file "message.txt"))
(define t (read-file2 "message.txt"))
(define p (open-input-file "message.txt"))
(define q (open-output-file "test.txt"))
