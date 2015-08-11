(define prehash
  ;; hack to figure out whether running 'mit-scheme' or 'scm'
  (let ((mit-scheme? (not (= 1 (inexact->exact 1.2)))))
    (lambda (x)
      (if mit-scheme?
        (equal-hash x)          ; value based hash for mit-scheme
        (hash x 1000000000))))) ; value based hash for scm

(define dictionary
  ;;
  ;;
  (lambda()
  ;;
  ;; private data
  (let ((data (make-vector 4))  ;; initial space allocation for 4 entries
        (num 0)                 ;; number of entries
        (size 4))               ;; allocated space
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'insert!) insert!)  ; overwrites value on duplicate key
          ((eq? m 'delete!) delete!)  ; deletes key from dictionary if it exists
          ((eq? m 'find!) search)     ; returns pair (key . value) or #f if fails
          (else (display "hash: unknown operation error\n"))))
  ;; private members
  ;;
  (define (insert! key value)
    'done)
  ;;
  ;;
  (define (delete! key)
    'done)
  ;;
  ;;
  (define (search key)
    'done)
  ;;
  (define (hash key)
    (modulo (prehash key) size))
  ;; returning interface
  dispatch)))
