(load "bst-node.scm")

(define (bst proc)  ; 'proc' strict total order between keys
  ;;
  ;;private data
  (let ((less? proc) ; procedure allowing comparision < between keys
        (top '()))   ; top node of bst
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'insert!) insert!); overwrites value on duplicate key
          ((eq? m 'delete!) delete!); deletes key from tree if it exists
          ((eq? m 'min) (find-min)) ; returns pair (key value)
          ((eq? m 'max) (find-max)) ; returns pair (key value)
          ((eq? m 'find) search)    ; returns pair (key value) or #f if no key
          ((eq? m 'succ) succ)      ; returns pair (key value) or #f if no succ
          ((eq? m 'pred) pred)      ; returns pair (key value) or #f if no pred
          ((eq? m 'check) (check))  ; returns #t if all checks are successful
          (else (display "bst: unknown operation error\n"))))
  ;;
  ;; private members
  ;;
  ;; insert (key value) into tree by inserting (key value)
  ;; into top node and adjusting top node to point to the
  ;; modified tree. Insert on duplicate keys will overwrite
  ;; value
  ;;
  (define (insert! key value)
    (set! top (insert-node! top key value)))
  ;;
  (define (delete! key)
    (set! top (delete-node! top key)))
  ;;
  ;; returns pair (key value) where key is the min key
  ;;
  (define (find-min)
    (let ((node (find-min-node top)))
      (cons (node 'key) (node 'value))))
  ;;
  ;; returns pair (key value) where key is the max key
  ;;
  (define (find-max)
    (let ((node (find-max-node top)))
      (cons (node 'key) (node 'value))))
  ;;
  ;; returns pair (key value) if 'key' successfully found
  ;; returns #f otherwise. Returning the pair (key value)
  ;; as opposed to simply 'value' removes the potential
  ;; ambiguity of a return value being #f.
  (define (search key)
    (let ((node (search-node top key)))
      (if (null? node)
        #f
        (cons (node 'key) (node 'value)))))
  ;;
  ;; returns pair (key value) corresponding to successor of 'key'
  ;; returns #f if no successor exists
  (define (succ key)
    (let ((node (succ-node top key)))
      (if (null? node)
        #f
        (cons (node 'key) (node 'value)))))
  ;;
  ;; returns pair (key value) corresponding to predecessor of 'key'
  ;; returns #f if no predecessor exists
  (define (pred key)
    (let ((node (pred-node top key)))
      (if (null? node)
        #f
        (cons (node 'key) (node 'value)))))
  ;;
  ;; checks tree is a properly formed binary search tree
  (define (check)
    (cond ((not (check-invariant-node top)) #f)
          ((not (check-parent-node top)) #f)
          ((and (not (null? top)) (not (null? (top 'parent)))) #f)
          (else #t)))
  ;;
  (define (insert-node! node key value)
    (cond ((null? node)             ; tree referred to by 'node' is empty
           (bst-node key value))    ; returning new node
          ((less? key (node 'key))  ; should insert from the left
           ((node 'set-left!) (insert-node! (node 'left) key value))
           (((node 'left) 'set-parent!) node)
           node)                    ; returning original node with new left child
          ((less? (node 'key) key)  ; should insert from the right
           ((node 'set-right!) (insert-node! (node 'right) key value))
           (((node 'right) 'set-parent!) node)
           node)                    ; returning original node with new right child
          ;; both < and > have failed. Case of duplicate keys.
          (else
            ((node 'set-value) value)
            node)))
  ;;
  (define (find-min-node node)    ; returns node with min key from tree 'node'
    (cond ((null? node) '())
          ((null? (node 'left)) node)
          (else (find-min-node (node 'left)))))
  ;;
  (define (find-max-node node)    ; returns node with max key from tree 'node'
    (cond ((null? node) '())
          ((null? (node 'right)) node)
          (else (find-max-node (node 'right)))))
  ;;
  ;; returns the node with 'key' from tree referred to by 'node'
  ;; returns '() if 'key' not present.
  (define (search-node node key)
    (cond ((null? node) '())
          ((less? key (node 'key)) (search-node (node 'left) key))
          ((less? (node 'key) key) (search-node (node 'right) key))
          ;; both < and > have failed. key found. returning 'node'
          (else node)))
  ;;
  ;; returns the node whose key is the successor of 'key' within
  ;; the tree referred to by 'node'. The successor is the smallest
  ;; key which is greater than 'key'. Returns '() if no successor exists.
  (define (succ-node node key)
    (cond ((null? node) '())
          ;; key if to the left
          ((less? key (node 'key))
           ;; looking for successor key in left sub-tree
           (let ((n (succ-node (node 'left) key)))
             (if (null? n)  ; there is no successor of key in left sub-tree
               node         ; current node contains the successor key
               n)))         ; successor key of left sub-tree is successor key
          ;; key is to the right
          ((less? (node 'key) key)
           (succ-node (node 'right) key)) ; successor must be in right sub-tree
          ;; key is that of 'node'
          (else
            (if (null? (node 'right))           ; no right sub-tree exists
              (let ((n (node 'parent)))         ; successor possibly parent
                (cond ((null? n) '())           ; no successor if no parent
                      ((less? key (n 'key)) n)  ; parent key greater => it is succ
                      ((less? (n 'key) key) '()); parent key smaller =>  no succ
                      (else (display "bst: duplicate key error\n"))))
              ;; otherwise successor key is min of right sub-tree
              (find-min-node (node 'right))))))
  ;;
  ;; returns the node whose key is the predecessor of 'key' within
  ;; the tree referred to by 'node'. The predecessor is the largest
  ;; key which is smaller than 'key'. Returns '() if no predecessor exists.
  (define (pred-node node key)
    (cond ((null? node) '())
          ;; key if to the right
          ((less? (node 'key) key)
           ;; looking for predecessor key in right sub-tree
           (let ((n (pred-node (node 'right) key)))
             (if (null? n)  ; there is no predecessor of key in right sub-tree
               node         ; current node contains the predecessor key
               n)))         ; predecessor key of right sub-tree is predecessor key
          ;; key is to the left
          ((less? key (node 'key))
           (pred-node (node 'left) key)) ; predecessor must be in left sub-tree
          ;; key is that of 'node'
          (else
            (if (null? (node 'left))            ; no left sub-tree exists
              (let ((n (node 'parent)))         ; predecessor possibly parent
                (cond ((null? n) '())           ; no predecessor if no parent
                      ((less? (n 'key) key) n)  ; parent key smaller => it is pred
                      ((less? key (n 'key)) '()); parent key greater =>  no pred
                      (else (display "bst: duplicate key error\n"))))
              ;; otherwise predecessor key is max of left sub-tree
              (find-max-node (node 'left))))))
  ;;
  ;; The following procedure (with side effects) takes a 'node' argument
  ;; which is interpreted as a tree, and returns a new node, representing
  ;; a new tree where the maximal key has been placed at the top with no
  ;; right child. This operation is needed for deletion of keys.
  ;; This operation has no effect on empty trees.
  ;;
  (define (root-max-node! node)
    (cond ((null? node) node)
          ((null? (node 'right))
           ((node 'set-parent!) '())
           node)  ; no right child, max node on the top
          (else ; max node is not at the top, some work is required
            (let ((n (root-max-node! (node 'right)))) ; recursive call
              ((node 'set-right!) (n 'left))    ; new right child without max
              (if (not (null? (node 'right)))   ; if new right child exists ...
                (((node 'right) 'set-parent!) node))  ; ... then set up parent
              ((n 'set-left!) node)             ; node getting to the left of max
              ((node 'set-parent!) n)           ; not forgetting parent link
              n))))                             ; returning max node
  ;;
  ;; The following procedure (with side effects) takes a 'node' argument
  ;; which is interpreted as a tree, and returns a new node, representing
  ;; a new tree where the minimal key has been placed at the top with no
  ;; left child. This operation is needed for deletion of keys.
  ;; This operation has no effect on empty trees.
  ;;
  (define (root-min-node! node)
    (cond ((null? node) node)
          ((null? (node 'left))
           ((node 'set-parent!) '())
           node)  ; no left child, min node on the top
          (else ; min node is not at the top, some work is required
            (let ((n (root-min-node! (node 'left)))) ; recursive call
              ((node 'set-left!) (n 'right))    ; new left child without min
              (if (not (null? (node 'left)))    ; if new left child exists ...
                (((node 'left) 'set-parent!) node))  ; ... then set up parent
              ((n 'set-right!) node)            ; node getting to the right of min
              ((node 'set-parent!) n)           ; not forgetting parent link
              n))))                             ; returning min node
  ;;
  ;; Returns the top node of the tree obtained after deletion of the
  ;; node corresponding to the 'key' argument from the tree whose
  ;; top node is the 'node' argument. This should have no impact
  ;; unless 'key' is part of the original tree.
  ;;
  ;; The implementation is somewhat arbitrary in the sense that whenever
  ;; the key to be deleted is at the top of the tree, and both children
  ;; exist, it chooses to promote the successor rather than the predecessor
  ;; at the top of the new tree.
  ;;
  (define (delete-node! node key)
    (cond ((null? node) node)       ; nothing to do on empty tree
          ((less? key (node 'key))  ; key to be deleted is on the left
           ;; new left child is that obtained after deletion of key
           (let ((new (delete-node! (node 'left) key)))
             ((node 'set-left!) new)
             (if (not (null? new)) ((new 'set-parent!) node))
             node)) ; return original node after modification
          ((less? (node 'key) key)  ; key to be deleted is on the right
           ;; new right child is that obtained after deletion of key
           (let ((new (delete-node! (node 'right) key)))
             ((node 'set-right!) new)
             (if (not (null? new)) ((new 'set-parent!) node))
             node)) ; return original node after modification
          ;; at this stage key to be deleted is (node 'key)
          ((null? (node 'left))       ; left child does not exist
           (let ((new (node 'right))) ; candidate for tree after deletion
             (if (not (null? new)) ((new 'set-parent!) '()))
             new))
          ((null? (node 'right))      ; left child does exist but right doesn't
           (let ((new (node 'left)))
             ((new 'set-parent!) '())
             new))
          ;; at this stage both left and right children exist, while top
          ;; key needs to be deleted. We arbitrarily choose to promote
          ;; successor at the top of new tree.
          (else
            ;; 'new' is right child after its minimum has been brought to the
            ;; top. (The minimum of the right child is the successor)
            ;; note that 'new' should have no left child since min is at the top.
            (let ((new (root-min-node! (node 'right))))
              ((new 'set-left!) (node 'left)) ; gluing initial left child
              (((new 'left) 'set-parent!) new); not forgetting to set parent
              new))))

  ;;
  ;; checks that tree referred to by 'node' has the binary search tree
  ;; property. Returns #t if that is the case and #f otherwise.
  (define (check-invariant-node node)
    (cond ((null? node) #t)
          ((not (check-invariant-node (node 'left))) #f)
          ((not (check-invariant-node (node 'right))) #f)
          ;; if left child exists, every key to the left has to be smaller
          ((and (not (null? (node 'left)))
                (less? (node 'key) ((find-max-node (node 'left)) 'key))) #f)
          ;; if right child exists, every key to the right has to be larger
          ((and (not (null? (node 'right)))
                (less? ((find-min-node (node 'right)) 'key) (node 'key))) #f)
          ;; every test was passed succesfully
          (else #t)))
  ;; checks that every child has the appropriate parent pointer
  (define (check-parent-node node)
    (cond ((null? node) #t)
          ((not (check-parent-node (node 'left))) #f)
          ((not (check-parent-node (node 'right))) #f)
          ;; if left child exists, its parent pointer should refer to 'node'
          ((and (not (null? (node 'left)))
                (not (eq? node ((node 'left) 'parent)))) #f)
          ;; if right child exists, its parent pointer should refer to 'node'
          ((and (not (null? (node 'right)))
                (not (eq? node ((node 'right) 'parent)))) #f)
          ;; every test was passed succesfully
          (else #t)))
  ;;
  ;; primitive printout used for debugging
  (define (print-node node)
    (if (null? node)
      (display ".")
      (begin (display "( ") (display (node 'key)) (display " ( ")
             (print-node (node 'left)) (display " , ")
             (print-node (node 'right)) (display " ) )"))))
  ;;
  ;; returning interface
  dispatch))
