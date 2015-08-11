(define (avl-node key value)
  ;;
  ;; private data
  (let ((key key)
        (left '())
        (right '())
        (parent '())
        (value value)
        (height -1))
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'key) key)
          ((eq? m 'left) left)
          ((eq? m 'right) right)
          ((eq? m 'parent) parent)
          ((eq? m 'value) value)
          ((eq? m 'height) height)
          ((eq? m 'set-value!) set-value!)
          ((eq? m 'set-height!) set-height!)
          ((eq? m 'set-left!) set-left!)
          ((eq? m 'set-right!) set-right!)
          ((eq? m 'set-parent!) set-parent!)
          (else (display "avl-node: unknown operation error\n"))))
  ;;
  ;; private members
  ;;
  (define (set-value! new)
    (set! value new))
  ;;
  (define (set-height! new)
    (set! height new))
  ;;
  (define  (set-left! node)
    (set! left node))
  ;;
  (define (set-right! node)
    (set! right node))
  ;;
  (define (set-parent! node)
    (set! parent node))
  ;;
  ;; returning interface
  dispatch))


