(require 'macro)  

(define-syntax stream-cons
  (syntax-rules
    ()
    ((stream-cons expr1 expr2)        
     (stream expr1 (delay expr2)))))

(define (ints n)
  (delay (cons n (ints (+ n 1)))))

(define (fcar l)
  (car (force l)))

(define (fcdr l)
  (cdr (force l)))

(define seq (ints 0))
(display (fcar seq))(newline)
(display (fcar (fcdr seq))) (newline)
(display (fcar (fcdr (fcdr seq))))(newline)

(define (pascal seq)
  (delay (cons seq (pascal (add-list (shift-left seq) (shift-right seq))))))

(define (shift-left seq)
  (append seq '(0)))

(define (shift-right seq)
  (cons 0 seq))

(define (add-list seq1 seq2)
  (cond ((null? seq1) '())
        ((null? seq2) '())
        (else (cons (+ (car seq1) (car seq2))
                    (add-list (cdr seq1) (cdr seq2))))))

(define pas (pascal '(1)))

(display (fcar pas))(newline)
(display (fcar (fcdr pas)))(newline)
(display (fcar (fcdr (fcdr pas))))(newline)
(display (fcar (fcdr (fcdr (fcdr pas)))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr pas))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas))))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas))))))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas))))))))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas))))))))))))))))))))(newline)
(display (fcar (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr (fcdr pas)))))))))))))))))))))(newline)

(define (pascal2 n row)
  (if (= 1 n) (list row)
    (cons row (pascal2 (- n 1)
                       (add-list (shift-left row)
                                 (shift-right row))))))
(display (pascal2 10 '(1)))(newline)

(define (op-list op l1 l2)
  (cond ((null? l1) '())
        ((null? l2) '())
        (else (cons (op (car l1) (car l2)) (op-list op (cdr l1) (cdr l2))))))

(define (gen-pascal op n)
  (if (= 1 n) '(1)
    ; else
    (let ((l (gen-pascal op (- n 1))))
      (op-list op (shift-left l) (shift-right l)))))

(define counter
(let ((c 0))
  (let ((read (lambda () c))
        (bump! (lambda() (set! c (+ 1 c)))))
    (cons read bump!))))



