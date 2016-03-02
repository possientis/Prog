(require 'hash-table)

(define frame4
  (let ((_static #f))
    ; object created is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'empty?) (empty? data))
              ((eq? m 'insert!)(insert! data))
              ((eq? m 'delete!)(delete! data))
              ((eq? m 'find)   (search data))
              ((else (error "frame4: unknown operation error: " m))))))
    ;
    ; implementation of public interface
    ;
    (define (empty? data) (eq? 0 (count data)))
    ;
    (define (insert! data)
      (lambda (key value)
        (let ((found (hash-find key (table data))))
          (if (eq? #f found)                  ; key not already present
            (set-car! data (+ (car data) 1))) ; increasing element count
          (hash-insert! (table data) key value))))
    ;
    (define (delete! data)
      (lambda (key)
        (let ((found (hash-find key (table data))))
          (if (not (eq? #f found))            ; key *is* present
            (set-car! data (- (car data) 1))) ; decreasing element count
          (hash-delete! (table data) key))))
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
    ; accessors
    ;
    (define (count data) (car data))    ; number of elements in table
    ;
    (define (size data) (cadr data))    ; size of hash table
    ;
    (define (table data) (caddr data))  ; hash table object
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



