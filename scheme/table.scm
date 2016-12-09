;; running unit-test on file loading
(table::unit-test)
;;
(define (table) ; returns a table object as procedure
  ;;
  (define data '()) ; list of ordered pairs (key,value)
  ;;
  ;;
  (define (findpair key subtable)
    (cond ((null? subtable) #f)
          ((equal? key (caar subtable)) (car subtable))
          (else (findpair key (cdr subtable)))))
  ;;
  ;;
  (define (deletepair key subtable)   ; returns subtable with deleted item
    (cond ((null? subtable) '())
          ((equal? key (caar subtable)) (cdr subtable))
          (else (cons (car subtable) (deletepair key (cdr subtable))))))
  ;;
  ;;
  (define (get key)   ; returns value associated with key, or #f
    (let ((pair (findpair key data)))
      (if (eq? #f pair)
        #f
        (cdr pair))))
  ;;
  ;;
  (define (insert! key value)    ; inserts new pair (key,value) or updates value
    (let ((pair (findpair key data)))
      (if (eq? #f pair)
        (set! data (cons (cons key value) data))
        (set-cdr! pair value)))
    data)
  ;;
  ;;
  (define (delete! key)        ; removes pair (key,value) from table, if present
    (set! data (deletepair key data))
    data)
  ;;
  ;;
  (define (dispatch m)
    (cond ((eq? m 'get) get)
          ((eq? m 'insert) insert!)
          ((eq? m 'delete) delete!)
          ((eq? m 'show) data)
          (else "table: unknown operation error")))
  dispatch)


(define (table::unit-test)
    ;;
    (define a (table))
    (define b (table))
    ;;
    (print "table.scm : running unit test")
    ;;
    ;; checking inserts
    ((a 'insert) 'foo 45)
    ((a 'insert) "bar" 56)
    ((a 'insert) 30 "test")
    (if (not (= 45 ((a 'get) 'foo))) (print "table: error get foo"))
    (if (not (= 56 ((a 'get) "bar"))) (print "table: error get bar"))
    (if (not (equal? "test" ((a 'get) 30))) (print "table: error get 30"))
    ;; checking inserts on new table has no impact
    ((b 'insert) 'foo 46)
    ((b 'insert) "bar" 57)
    ((b 'insert) 30 "test2")
    (if (not (= 45 ((a 'get) 'foo))) (print "table: error get foo"))
    (if (not (= 56 ((a 'get) "bar"))) (print "table: error get bar"))
    (if (not (equal? "test" ((a 'get) 30))) (print "table: error get 30"))
    ;; checking inserts with new values on existing keys
    ((a 'insert) 'foo 452)  ; new values
    ((a 'insert) "bar" 562)
    ((a 'insert) 30 "test2")
    (if (not (= 452 ((a 'get) 'foo))) (print "table: error get foo"))
    (if (not (= 562 ((a 'get) "bar"))) (print "table: error get bar"))
    (if (not (equal? "test2" ((a 'get) 30))) (print "table: error get 30"))
    ;; checking delete
    ((a 'delete) 'foo)
    (if (not (eq? #f ((a 'get) 'foo))) (print "table: error as foo deleted"))
    ((a 'delete) 'foo)      ; should have no impact
    ((a 'delete) "bar")
    (if (not (eq? #f ((a 'get) "bar"))) (print "table: error as bar deleted"))
    ((a 'delete) "bar")     ; should have no impact
    ;; checking inserts after delete
    ((a 'insert) 'foo 45)   ; checking inserts still successful after delete
    ((a 'insert) "bar" 56)
    ((a 'insert) 30 "test")
    (if (not (= 45 ((a 'get) 'foo))) (print "table: error get foo"))
    (if (not (= 56 ((a 'get) "bar"))) (print "table: error get bar"))
    (if (not (equal? "test" ((a 'get) 30))) (print "table: error get 30"))
    ;;
    (print "table:scm : unit test complete"))

