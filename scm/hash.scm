(load "link.scm")


(define dictionary
  ;;
  ;; static private member
  (let ((prehash
        ;; hack to figure out whether running 'mit-scheme' or 'scm'
        (let ((mit-scheme? (not (= 1 (inexact->exact 1.2)))))
          (lambda (x)
            (if mit-scheme?
              (equal-hash x)          ; value based hash for mit-scheme
              (hash x 1000000000)))))); value based hash for scm
  ;;
  (lambda(proc)                 ; 'proc' procedure testing equality between keys
  ;;
  ;; private data
  (let ((data (make-vector 4))  ; initial allocation
        (num 0)                 ; number of entries
        (size 4)                ; allocated space
        (same-key? proc)        ; procedure determining equality between keys
        (mem-enabled? #t))      ; flag enabling memory allocation or deallocation
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'insert!) insert!)  ; overwrites value on duplicate key
          ((eq? m 'delete!) delete!)  ; deletes key from dictionary if it exists
          ((eq? m 'find) search)      ; returns pair (key . value) or #f if fails
          ((eq? m 'debug) (debug))    ; implementation specific debug info
          ((eq? m 'check) (check))    ; some sanity checks, returns #f if fails
          ((eq? m 'prehash) prehash)    ; exporting static function
          (else (display "hash: unknown operation error\n"))))
  ;; private members
  ;;
  (define (insert! key value)
    (let ((h (hash key)))
      (if (null? (vector-ref data h))      ; no existing entry for this hash value
        (vector-set! data h (link same-key?))); allocating linked list to entry h
      ;; entry with hash value h has an associated linked list
      (if (eq? #f (((vector-ref data h) 'find) key))  ; key is new in table
        (set! num (+ 1 num)))    ; counter incremented only if new key
      (((vector-ref data h) 'insert!) key value))) ; insert into linked list
  ;;
  ;;
  (define (delete! key)
    (let ((h (hash key)))
      (let ((h-list (vector-ref data h)))
        (if (null? h-list)
          'done   ; nothing to do
          (begin
            (if (not (eq? #f ((h-list 'find) key))) ; key present in table
              (set! num (- num 1))) ; counter decremented only if key present
            ((h-list 'delete!) key))))))
  ;;
  (define (search key)
    (let ((h (hash key)))
      (if (null? (vector-ref data h))
        #f  ; hash value not in table, hence key not in table
        (((vector-ref data h) 'find) key))))
  ;;
  (define (need-increase?)  ;; decides whether more space needed
    (> (/ num size) 0.5))   ;; increase when load factor > 50%
  ;;
  (define (need-decrease?)  ;; decides whether to reduce space allocation
    (and (>= size  8) (< (/ num size) 0.25)))
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
  ;;
  (define (debug)
    (display "----------------------------\n")
    (display "Hash table debug:\n")
    (display "Allocated vector size: ")
    (display (vector-length data))
    (newline)
    (display "Maintained vector size: ")
    (display size)
    (newline)
    (display "Number of elements: ")
    (display num)
    (newline)
    (let loop ((i 0))
      (if (< i (vector-length data))
        (begin
          (display "entry ")
          (display i)
          (display ": ")
          (if (null? (vector-ref data i))
            (display "'()")
            (let loop2 ((iter ((vector-ref data i) 'iter)))
              (if (not (iter 'null?))
                (begin
                  (display "key = ")
                  (display (iter 'key))
                  (display ": value = ")
                  (display (iter 'value))
                  (display "   ")
                  (iter '++)
                  (loop2 iter)))))
          (newline)
          (loop (+ 1 i)))))
    (display "----------------------------\n"))
  ;;
  (define (check)
    (cond ((not (= size (vector-length data))) #f)
          ((not mem-enabled?) #f)   ; mem-enabled? should be restored to #t
          ((need-increase?) #f)     ; new allocation failed to take place
          ((need-decrease?) #f)     ; freeing of memory failed to take place
          (else ; counting table entries
            (let ((count 0))
              (let loop ((i 0))
                (if (< i size)
                  (begin
                    (if (not (null? (vector-ref data i)))
                      (let loop2 ((iter ((vector-ref data i) 'iter)))
                        (if (not (iter 'null?))
                          (begin
                            (set! count (+ 1 count))  ; one more element
                            (iter '++)
                            (loop2 iter)))))
                    (loop (+ 1 i)))))
              (if (not (= count num))
              #f      ; counted number of elements does not fit expectation
              #t))))) ; all sanity checks were succesful


  ;; initializing vector
  (vector-fill! data '())
  ;; returning interface
  dispatch))))
