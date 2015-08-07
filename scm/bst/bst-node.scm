(define (bst-node key value)
  ;;
  ;; private data
  (let ((key key)
        (left '())
        (right '())
        (parent '())
        (value value))
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'key) key)
          ((eq? m 'left) left)
          ((eq? m 'right) right)
          ((eq? m 'parent) parent)
          ((eq? m 'value) value)
          ((eq? m 'set-value!) set-value!)
          ((eq? m 'set-left!) set-left!)
          ((eq? m 'set-right!) set-right!)
          ((eq? m 'set-parent!) set-parent!)
          (else (display "bst-node: uknown operation error\n"))))
  ;;
  ;; private members
  ;;
  (define (set-value! new)
    (set! value new))
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


