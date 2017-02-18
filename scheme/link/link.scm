;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-link)) 
  (begin
    (define included-link #f)
    (display "loading link")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(load "link-node.scm")

(define link  ; constructor
  (let ((let-for-name-encapsulation #t))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'insert!) (insert! data))
              ((eq? m 'delete!) (delete! data))
              ((eq? m 'find)    (search data))  ; find symbol already bound
              ((eq? m 'empty?)  (empty? data))
              ((eq? m 'iter)    ((iter data)))    ; returns an iterator object
              ((eq? m 'print)   (print data))
              (else (error "link:unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (empty? data) (null? (head data)))
    ;
    (define (insert! data)
      (lambda (key value)
        (set-head! data (insert-node! (head data) key value (same-key? data)))))
    ;
    (define (delete! data)
      (lambda (key)
        (set-head! data (delete-node! (head data) key (same-key? data)))))
    ;
    (define (search data)
      (lambda (key)
        (search-node (head data) key (same-key? data))))
    ;
    (define (print data)
      (display "( ")(print-node (head data))(display ")"))
    ;
    ; private helper function
    ;
    (define (head data) (cadr data))
    ;
    (define (same-key? data) (caddr data))
    ;
    (define (set-head! data new-value) (set-car! (cdr data) new-value))
    ;
    (define (insert-node! node key value proc)
      (cond ((null? node) (link-node key value))
            ((proc key (node 'key))     ; duplicate key
              ((node 'set-value!) value) ; updating value of existing key
              node)                      ; returning original node
            (else (let ((next (node 'next)))
                    ((node 'set-next!) (insert-node! next key value proc))
                    node))))
    ;
    (define (delete-node! node key proc)
      (cond ((null? node) '())        ; no impact on empty list
            ((proc key (node 'key)) (node 'next)) ; key found, return next
            (else (let ((next (node 'next)))
                    ((node 'set-next!) (delete-node! next key proc))
                   node))))
    ;
    (define (search-node node key proc)
      (cond ((null? node) #f) ; search failure
            ((proc key (node 'key)) (cons (node 'key) (node 'value)))
            (else (search-node (node 'next) key proc))))
    ;
    (define (print-node node)
      (if (null? node)
        (display "")
        (begin
          (display (node 'key))
          (display " ")
          (print-node (node 'next)))))
    ;
    ; iterator nested class
    ;
    (define (iter data)  ; constructor
      ; object created from data is message passing interface
      (define (this iter-data)
        (lambda (m)
          (cond ((eq? m '++) (iter-move! iter-data))
                ((eq? m 'null?) (iter-null? iter-data))
                ((eq? m 'key)   (iter-key iter-data))
                ((eq? m 'value) (iter-value iter-data))
                (else (error "link: unknown iterator operation error" m)))))
      ;
      ; implementation of public interface
      ;
      (define (iter-move! iter-data)
        (set-car! (cdr iter-data) ((node iter-data) 'next)))
      ;
      (define (iter-null? iter-data) (null? (node iter-data)))
      ;
      (define (iter-key iter-data) ((node iter-data) 'key))
      ;
      (define (iter-value iter-data) ((node iter-data) 'value))
      ;
      (define (node iter-data) (cadr iter-data))
      ;
      ; returning no argument constructor
      (lambda () (this (list 'data  (head data)))))
    ;
    ; returning single argument constructor
    ;
    (lambda (same-key?)
      (this (list 'data '() same-key?)))))


))  ; include guard
