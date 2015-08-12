(load "link.scm")

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
  (lambda(proc)                 ; 'proc' procedure testing equality between keys
  ;;
  ;; private data
  (let ((data (make-vector 4))  ; initial space allocation for 4 entries
        (num 0)                 ; number of entries
        (size 4)                ; allocated space
        (same-key? proc)        ; procedure determining equality between keys
        (mem-enabled? #t))      ; flag enabling memory allocation or deallocation
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
    (let ((h (hash key)))
      (if (null? (vector-ref data h)) ; no existing entry for this hash value
        (vector-set! data h 12))))
  ;;
  ;;
  (define (delete! key)
    'done)
  ;;
  ;;
  (define (search key)
    'done)
  ;;
  (define (need-increase?)  ;; decides whether more space needed
    (> (/ num size) 0.5))   ;; increase when load factor > 50%
  ;;
  (define (need-decrease?)  ;; decides whether to reduce space allocation
    (and (size >= 8) (< (/ num size) 0.25)))
  ;;
  (define (hash key)
    (modulo (prehash key) size))
  ;;
  (define (increase!)
    (if (not mem-enabled?)
      (begin (display "hash: illegal call to increase! method\n") 'done)
      (begin
        (if (need-increase?)
          (let ((new (make-vector (* 2 size))))
            'done)))))




  ;; returning interface
  dispatch)))
