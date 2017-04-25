(use-modules (srfi srfi-1) (srfi srfi-13))

(define (my-hash str size)
  (remainder (string-hash-ci str) size))

(define (my-assoc str alist)
  (find (lambda (pair) (string-ci=? str (car pair))) alist))

(define my-table (make-hash-table))   ; suitable for any hash , hashq, hashv and custom hash

(hashx-set! my-hash my-assoc my-table "foo" 123)

(display (hashx-ref my-hash my-assoc my-table "FOO"))(newline)
