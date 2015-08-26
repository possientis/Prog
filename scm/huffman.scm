(define (make-leaf symbol weight)
  (list 'leaf symbol weight))

(define (leaf? object)
  (and (pair? object) (eq? (car object) 'leaf)))

(define (symbol-leaf x) (cadr x))

(define (weight-leaf x) (caddr x))

(define (left-branch tree) (car tree))

(define (right-branch tree) (cadr tree))

(define (symbols tree)
  (if (leaf? tree)
    (list (symbol-leaf tree))
    (caddr tree)))

(define (weight tree)
  (if (leaf? tree)
    (weight-leaf tree)
    (cadddr tree)))

(define (choose-branch bit branch)
  (cond ((eq? bit #f) (left-branch branch))
        ((eq? bit #t) (right-branch branch))
        (else (display "huffman: bad bit in choose-branch\n"))))

(define (make-code-tree left right)
  (list left
        right
        (append (symbols left) (symbols right))
        (+ (weight left) (weight right))))


(define (decode bits tree)
  (define (decode-1 bits current-branch)
    (if (null? bits)
      '()
      (let ((next-branch
              (choose-branch (car bits) current-branch)))
        (if (leaf? next-branch)
          (cons (symbol-leaf next-branch)
                (decode-1 (cdr bits) tree))
          (decode-1 (cdr bits) next-branch)))))
  (decode-1 bits tree))

(define (adjoin-set x set)
  (cond ((null? set) (list x))
        ((< (weight x) (weight (car set))) (cons x set))
        (else (cons (car set)
                    (adjoin-set x (cdr set))))))


(define sample-tree
  (make-code-tree (make-leaf 'A 4)
                  (make-code-tree
                    (make-leaf 'B 2)
                    (make-code-tree (make-leaf 'D 1)
                                    (make-leaf 'C 1)))))

(define sample-message '(#f #t #t #f #f #t #f #t #f #t #t #t #f))


(define (encode message tree)
  (if (null? message)
    '()
    (append (encode-symbol (car message) tree)
            (encode (cdr message) tree))))

(define (element-of-set? x set)
  (cond ((null? set) #f)
        ((eq? x (car set)) #t)
        (else (element-of-set? x (cdr set)))))

(define (encode-symbol symbol tree)
  (cond ((leaf? tree)
         (if (eq? symbol (symbol-leaf tree))
           '()
           (display "huffman: error in encode-symbol\n")))
        ((element-of-set? symbol (symbols (left-branch tree)))
         (cons #f (encode-symbol symbol (left-branch tree))))
        ((element-of-set? symbol (symbols (right-branch tree)))
         (cons #t (encode-symbol symbol (right-branch tree))))
        (else (display "huffman: unexpected symbol in encode-symbol\n"))))


(define (make-leaf-set pairs)
  (if (null? pairs)
    '()
    (let ((pair (car pairs)))
      (adjoin-set (make-leaf (car pair)
                             (cadr pair))
                  (make-leaf-set (cdr pairs))))))


(define (generate-huffman-tree pairs)
  (successive-merge (make-leaf-set pairs)))

(define (successive-merge set)
  (if (= 1 (length set))
    set
    (successive-merge
      (adjoin-set
        (make-code-tree (car set) (cadr set))
        (cddr set)))))

(define sample-pairs
  (list
    (list 'a 45)
    (list 'd 16)
    (list 'b 13)
    (list 'c 12)
    (list 'e 9)
    (list 'f 5)))

(define new-pairs
  (list
    (list 'A 2)
    (list 'BOOM 1)
    (list 'GET 2)
    (list 'JOB 2)
    (list 'NA 16)
    (list 'SHA 3)
    (list 'YIP 9)
    (list 'WAH 1)))

(define tree (generate-huffman-tree sample-pairs))

(define message
  (list
    'get 'a 'job
    'sha 'na 'na 'na 'na 'na 'na 'na 'na
    'get 'a 'job
    'sha 'na 'na 'na 'na 'na 'na 'na 'na
    'wah 'yip 'yip 'yip 'yip 'yip 'yip 'yip 'yip
    'sha 'boom))


