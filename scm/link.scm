(load "link-node.scm")

(define link
  ;;
  ;; static private members
  (letrec (   ; recursive let needed for some procedure (e.g. print-node)
        ;;
        (insert-node!
          (lambda (node key value proc)
            (cond ((null? node) (link-node key value))
                  ((proc key (node 'key))     ; duplicate key
                   ((node 'set-value!) value) ; updating value of existing key
                   node)                      ; returning original node
                  (else (let ((next (node 'next)))
                          ((node 'set-next!) (insert-node! next key value proc))
                          node)))))
        ;;
        (delete-node!
          (lambda (node key proc)
            (cond ((null? node) '())        ; no impact on empty list
                  ((proc key (node 'key)) (node 'next)) ; key found, return next
                  (else (let ((next (node 'next)))
                          ((node 'set-next!) (delete-node! next key proc))
                        node)))))
        ;;
        (search-node
          (lambda (node key proc)
            (cond ((null? node) #f) ; search failure
                  ((proc key (node 'key)) (cons (node 'key) (node 'value)))
                  (else (search-node (node 'next) key proc)))))
        ;;
        (print-node
          (lambda (node)
            (if (null? node)
              (display "")
              (begin
                (display (node 'key))
                (display " ")
                (print-node (node 'next))))))
        )

  ;;
  (lambda (proc)    ; 'proc' procedure testing equality between keys
  ;;
  ;; private data
  (let ((same-key? proc)    ;
        (head '()))         ; head node of linked list
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'insert!) insert!)  ; overwrites value on duplicate key
          ((eq? m 'delete!) delete!)  ; deletes key from list if it exists
          ((eq? m 'find) search)      ; returns pair (key . value) or #f is fails
          ((eq? m 'iter) (iter))      ; returns an iterator interface
          ((eq? m 'print) (print))    ; basic display of keys
          (else (display "link: unknown operation error\n"))))
  ;;
  ;; private members
  ;;
  (define (insert! key value)
    (set! head (insert-node! head key value same-key?)))
  ;;
  (define (delete! key)
    (set! head (delete-node! head key same-key?)))
  ;;
  (define (search key)
    (search-node head key same-key?))
  ;;
  (define (iter)
    ;; private data of iterator initilized to start of list
    (let ((node  head))
      ;;
      ;; public interface of iterator
      (define (dispatch m)
        (cond ((eq? m '++) (set! node (node 'next)))
              ((eq? m 'null?) (null? node))
              ((eq? m 'key) (node 'key))
              ((eq? m 'value) (node 'value))
              (else (display "link: unknown iterator operation error\n"))))
      dispatch))
  ;;
  (define (print)
    (display "( ")
    (print-node head)
    (display ")"))

  ;;
  ;; returning interface
  dispatch))))
