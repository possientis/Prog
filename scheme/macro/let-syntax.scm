(define x (let ((/ +))
            (let-syntax ((divide (lambda (x)
                                   (syntax-case x ()
                                    ((_ e1 e2) (syntax (/ e1 e2)))))))
              (let ((/ *)) (divide 6 3)))))

(display "x = ")(display x)(newline)    ; 9 , not 18, not 2...

;(let-syntax ((divide (lambda (x) 
;                       (let ((/ +))
;                         (syntax-case x ()
                            ; cannot refer to '/' bound by let expression with transformer
;                           ((_ e1 e2) (syntax (/ e1 e2))))))))
;  (let ((/ *)) (divide 2 1))) ; unknown location: reference to identifier outside its scope in form
