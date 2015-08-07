(define (queue)
  ;;
  ;; private data
  (define first '())  ; points to first item in the queue
  (define last '())   ; points to last item in the queue
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'isempty?) (null? first))
          ((eq? m 'push!) push!)    ; insert at the end of the queue
          ((eq? m 'read!) (read!))  ; removes from the front of the queue
          (else "queue: unknown operation error")))
  ;;
  ;; private members
  ;;
  (define (push! x)    ; pushes value x at the end of the queue
    (let ((item (cons x '())))  ; item is list (x)
      (cond ((null? first)      ; queue empty
             (set! first item)
             (set! last item))
            (else
              (set-cdr! last item)  ; cdr of last is no longer ()
              (set! last item)))
      first))
  ;;
  (define (read!)      ; returns first entry and removes it from queue
    (cond ((null? first)        ; queue empty
           "queue: attempting to read empty queue error")
          (else
            (let ((item (car first)))
              (set! first (cdr first))
              item))))
  ;;
  ;; returning interface
  dispatch)
