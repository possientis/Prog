(require 'hash-table)
(require 'object->string)

(define frame4
  (let ((_static #f))
    ; object created is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'empty?) (empty? data))
              ((eq? m 'insert!)(insert! data))
              ((eq? m 'delete!)(delete! data))
              ((eq? m 'find)   (search data))
              ((eq? m 'to-string) (to-string data))
              ((else (error "frame4: unknown operation error: " m))))))
    ;
    ; implementation of public interface
    ;
    (define (empty? data) (eq? 0 (count data)))
    ;
    (define (to-string data)
      (let ((out "{") (start #t))
        (let ((add-item 
                (lambda (key val)
                  (set! out (string-append
                              out
                              (if start (begin (set! start #f) "") ", ")
                              (object->string key)
                              ": "
                              (object->string val))))))
          (hash-for-each add-item (table data))
          (string-append out "}"))))
    ;
    (define (insert! data)
      (lambda (key value)
        (let ((found (hash-find key (table data))))
          (if (eq? #f found)                  ; key not already present
            (set-car! data (+ (car data) 1))) ; increasing element count
          (hash-insert! (table data) key value)
          (resize-if-needed data))))
    ;
    (define (delete! data)
      (lambda (key)
        (let ((found (hash-find key (table data))))
          (if (not (eq? #f found))            ; key *is* present
            (set-car! data (- (car data) 1))) ; decreasing element count
          (hash-delete! (table data) key)
          (resize-if-needed data))))
    ;
    (define (search data) 
      (lambda (key) (hash-find key (table data))))
    ;
    ; private helper functions
    ;
    (define hash-find (predicate->hash-asso equal?))
    ;
    (define hash-insert! (hash-associator equal?))
    ;
    (define hash-delete! (hash-remover equal?))
    ;
    (define hash-resize (hash-rehasher equal?))
    ;
    ; accessors
    ;
    (define (count data) (car data))    ; number of elements in table
    ;
    (define (size data) (cadr data))    ; size of hash table
    ;
    (define (table data) (caddr data))  ; hash table object
    ;
    (define (table-load data) (/ (count data) (size data)))
    ;
    (define (need-increase? data) (> (table-load data) 0.8))
    ;
    (define (need-decrease? data) 
      (and (>= (size data) 8) (< (table-load data) 0.2)))
    ;
    (define (resize data new-size)
;      (display "resizing table: new size = ")(display new-size)(newline)
      (set-car! (cddr data) (hash-resize (table data) new-size)) 
      (set-car! (cdr data) new-size)) ; updating size
    ;
    (define (resize-if-needed data)
      (if (need-increase? data)
        (resize data (* (size data) 2))
        (if (need-decrease? data)
          (resize data (/ (size data) 2)))))
    ;
    ; returning no argument constructor (hash table has size 4 initially) 
    ;
    (lambda () (this (list 0 4 (make-hash-table 4))))))
       
; need to add resizing 

;(define x (frame4))
;(display (x 'empty?))(newline)
;((x 'insert!) 'a 2)
;((x 'insert!) 'b 3)
;((x 'insert!) 'c 4)
;((x 'insert!) 'd 5)
;((x 'insert!) 'e 6)
;(display ((x 'find) 'a))(newline)
;(display ((x 'find) 'a))(newline)
;(display ((x 'find) 'b))(newline)
;(display ((x 'find) 'c))(newline)
;(display ((x 'find) 'd))(newline)
;(display ((x 'find) 'e))(newline)
;((x 'delete!) 'e)
;(display ((x 'find) 'e))(newline)
;(display (x 'empty?))(newline)
;((x 'delete!) 'a)
;((x 'delete!) 'b)
;((x 'delete!) 'c)
;((x 'delete!) 'd)
;(display (x 'empty?))(newline)



