; implementation of standard lists a difference lists
(define diff-nil  ; returns empty list
  (cons '() '()))

(define (diff-cons a b)
  (cons (cons a (car b)) (cdr b)))

(define (diff-null? a)
  (eq? (car a) (cdr a)))

(define (diff-car a)
  (if (diff-null? a) (car '())  ; error
    (caar a)))

(define (diff-cdr a)
  (if (diff-null? a) (cdr '())  ; error
    (cons (cdar a) (cdr a))))

; converts difference list to standard list
(define (diff->list a)
  (if (diff-null? a) '()
    (cons (diff-car a) (diff->list (diff-cdr a)))))

; converts standard list to difference list
(define (list->diff a)
  (if (null? a) diff-nil
    (diff-cons (car a) (list->diff (cdr a)))))

; append operation is constant time for difference lists
(define (diff-append s1 s2)
  'ok)

(define x (list->diff '(0 1 2 3 4 5 6 7)))


