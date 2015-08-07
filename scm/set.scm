(define (entry tree) (car tree))

(define (left tree) (cadr tree))

(define (right tree) (caddr tree))

(define (make-tree entry left right)
  (list entry left right))

(define (element-of-set? x set)
  (cond ((null? set) #f)
        ((= x (entry set)) #t)
        ((< x (entry set))
         (element-of-set? x (left set)))
        ((> x (entry set))
         (element-of-set? x (right set)))))

(define (adjoin-set x set)
  (cond ((null? set) (make-tree x '() '()))
        ((= x (entry set)) set)
        ((< x (entry set))
         (make-tree (entry set)
                    (adjoin-set x (left set))
                    (right set)))
        ((> x (entry set))
         (make-tree (entry set)
                    (left set)
                    (adjoin-set x (right set))))))

(define (make-set l)
  (cond ((null? l) '())
        (else (adjoin-set (car l) (make-set (cdr l))))))

(define (set->list set)
  (if (null? set)
    '()
    (cons (entry set)
          (append
            (set->list (left set))
            (set->list (right set))))))


(define a (make-set '(0 1 2 3 4 5 6 7 8 9)))
