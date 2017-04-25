(define h (make-hash-table 31)) ; 31 slots


(display "h = ")(display h)(newline)

(hashq-set! h 'foo "bar")
(hashq-set! h 'bar "baz")
(hashq-set! h 'baz "foo")
(hashq-set! h 'hmm #f)     ; problem, key absent or value #f?

(display "(hashq-ref h 'foo) = ") (display (hashq-ref h 'foo))  (newline)
(display "(hashq-ref h 'bar) = ") (display (hashq-ref h 'bar))  (newline)
(display "(hashq-ref h 'baz) = ") (display (hashq-ref h 'baz))  (newline)
(display "(hashq-ref h 'hmm) = ") (display (hashq-ref h 'hmm))  (newline)
(display "(hashq-ref h 'not-there) = ")(display (hashq-ref h 'not-there))(newline)

; better use hashq-get-handle to distinguish between missing keys of #f values
(display "(hashq-get-handle h 'foo) = ") 
(display (hashq-get-handle h 'foo))(newline)

(display "(hashq-get-handle h 'bar) = ") 
(display (hashq-get-handle h 'bar))(newline)

(display "(hashq-get-handle h 'baz) = ") 
(display (hashq-get-handle h 'baz))(newline)

(display "(hashq-get-handle h 'hmm) = ") 
(display (hashq-get-handle h 'hmm))(newline)

(display "(hashq-get-handle h 'not-there) = ") 
(display (hashq-get-handle h 'not-there))(newline)

(hashq-set! h 'hmm "hmm")
(display "(hashq-ref h 'hmm) = ") (display (hashq-ref h 'hmm))  (newline)

(display (hash-fold (lambda (key value acc) (string-append acc value)) "" h))
(newline)

(display (hash-count (lambda (key value) (string? value)) h))
(newline)


(display (hash-count (const #t) h))
(newline)
