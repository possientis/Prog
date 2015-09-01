(load "link.scm")
(load "hash.scm")


(define dictionary
  ;;
  ;; private static member
  (let ((prehash ((hash-lib) 'prehash)))  ; prehash procedure from hash-lib module
  ;;
  (lambda()
  ;;
  ;; private data
  (let ((data (make-vector 4))  ; initial allocation
        (num 0)                 ; number of entries
        (size 4)                ; allocated space
        (mem-enabled? #t))      ; flag enabling memory allocation or deallocation
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'insert!) insert!)  ; overwrites value on duplicate key
          ((eq? m 'delete!) delete!)  ; deletes key from dictionary if it exists
          ((eq? m 'find) search)      ; returns pair (key . value) or #f if fails
          ((eq? m 'debug) (debug))    ; implementation specific debug info
          ((eq? m 'check) (check))    ; some sanity checks, returns #f if fails
          (else (display "dictionary: unknown operation error\n"))))
  ;; private members
  ;;
  (define (insert! key value)
    (let ((h (hash key)))
      (if (null? (vector-ref data h))   ; no existing entry for this hash value
        (vector-set! data h (link equal?))); allocating linked list to entry h
      (let ((link-list (vector-ref data h)))
        (if (eq? #f ((link-list 'find) key))  ; key not currently in table
          (set! num (+ 1 num)))               ; hence one more element in table
        ((link-list 'insert!) key value)))    ; insert into linked list
    (if mem-enabled? (increase!)))            ; allocates more space if required
  ;;
  ;;
  (define (delete! key)
    (let ((h (hash key)))
      (let ((link-list (vector-ref data h)))
        (if (null? link-list)
          'done   ; nothing to do
          (if (not (eq? #f ((link-list 'find) key)))  ; key exists
            (begin
              (set! num (- num 1))
              ((link-list 'delete!) key)
              ;; removing link list if empty
              (if (link-list 'empty?) (vector-set! data h '())))))))
    (if mem-enabled? (decrease!)))            ; de-allocates memory if required
  ;;
  (define (search key)
    (let ((h (hash key)))
      (let ((link-list (vector-ref data h)))
        (if (null? link-list) ; no link list defined for h, key not in table
          #f
          ((link-list 'find) key))))) ; searching for key in linked list
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
  ;; Linear time temporary vector of elements used to re-build hash table
  ;; following increase of decrease of allocated memory space.
  (define (temp-vector)     ;; returns a vector of all pairs (key . value)
    (let ((temp (make-vector num))) ;; allocating vector for all table elements
      (let ((index 0))              ;; storing index in new vector
        (let loop ((i 0))             ;; outer loop through hash table entries
          (if (< i (vector-length data))
            (begin
              (let ((link-list (vector-ref data i)))
                (if (not (null? link-list))
                  (let loop2 ((iter (link-list 'iter)))
                    (if (not (iter 'null?))
                      (begin
                        (vector-set! temp index (cons (iter 'key) (iter 'value)))
                        (set! index (+ index 1))
                        (iter '++)
                        (loop2 iter))))))
            (loop (+ i 1))))))
        temp))
  ;;
  ;; re-creating hash table from scratch with more allocated space to reduce load
  (define (increase!)
    (if (not mem-enabled?)          ; attempt at re-entry
      (begin (display "dictionary: illegal call to increase! method\n") 'done)
      (if (need-increase?)          ; increase only happens if needed
        (begin
          (set! mem-enabled? #f)    ; no more calls to increase! until set to #t
          (let ((new (make-vector (* 2 size)))
                (elems (temp-vector)))  ; whole table as vector (linear time)
            (set! data new)         ; new empty vector with double the size
            (vector-fill! data '()) ; initialization
            (set! size (* 2 size))  ;
            (set! num 0)            ;
            (let loop ((i 0))       ; looping through elements for new insertion
              (if (< i (vector-length elems))
                (begin
                  (let ((item (vector-ref elems i)))
                    (insert! (car item) (cdr item))); item is pair (key . value)
                  (loop (+ i 1))))))
          (set! mem-enabled? #t)))))

  ;;
  ;; re-creating hash table from scratch with less allocated space to free memory
  (define (decrease!)
    (if (not mem-enabled?)          ; attempt at re-entry
      (begin (display "dictionary: illegal call to decrease! method\n") 'done)
      (if (need-decrease?)          ; decrease only happens if needed
        (begin
          (set! mem-enabled? #f)    ; no calls to increase! until set to #t
          (let ((new (make-vector (/ size 2)))
                (elems (temp-vector)))  ; whole table as vector (linear time)
            (set! data new)         ; new empty vector with double the size
            (vector-fill! data '()) ; initialization
            (set! size (/ size 2))  ;
            (set! num 0)            ;
            (let loop ((i 0))       ; looping through elements for new insertion
              (if (< i (vector-length elems))
                (begin
                  (let ((item (vector-ref elems i)))
                    (insert! (car item) (cdr item))); item is pair (key . value)
                  (loop (+ i 1))))))
          (set! mem-enabled? #t)))))
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
    (newline)
    (display "Hash table entries as follows:\n")
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
    (newline)
    (display "Vector of elements as follows:\n")
    (display (temp-vector))
    (newline)
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
  ;;
  ;; initializing vector
  (vector-fill! data '())
  ;; returning interface
  dispatch))))
