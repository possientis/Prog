(use-modules (ice-9 regex))

(display (provided? 'regex))(newline) ; #t

; pattern is compiled into regex at each call => inefficient
(display (string-match "[0-9]+" "blah2017"))(newline)     ; #(blah2017 (4 . 8))
(display (string-match "[A-Za-z]" "1234567890"))(newline) ; #f


(define reg1 (make-regexp "[0-9]+"))

(display (regexp? reg1))(newline) ; #t 

(display (list-matches reg1 "blah2017"))(newline) ; (#(blah2017 (4 . 8)))

(define x (car (list-matches reg1 "blah2017")))

(display (regexp-match? x))(newline)    ; #t

(display (match:substring x))(newline)  ; 2017
