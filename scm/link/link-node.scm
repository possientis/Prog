(define (link-node key value)
  ;;
  ;; private data
  (let ((key key)
        (next '())
        (value value))
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'key) key)
          ((eq? m 'next) next)
          ((eq? m 'value) value)
          ((eq? m 'set-next!) set-next!)
          ((eq? m 'set-value!) set-value!)
          (else (display "link-node: unknown operation error\n"))))
  ;;
  ;; private members
  ;;
  (define (set-next! node)
    (set! next node))
  ;;
  (define (set-value! new)
    (set! value new))
  ;;
  ;; returning interface
  dispatch))

