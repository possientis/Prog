; This function should return #t when called under lazy evaluation
; and #f when called under strict evaluation. The function maintains
; a local variable **lazy?** which is initially set to #t. Then the
; function makes a call to '(try (unset-lazy)) where the function 
; 'try is designed such that it never uses its argument. Hence, 
; under lazy evaluation, the argument (unset-lazy) should not 
; be evaluated and **lazy?** should remain equal to #t. After
; the call to 'try, the function returns the value of **lazy?**

(define lazy?
  (let ((**lazy?** #t))
    (let ((unset-lazy 
            (lambda () 
              (set! **lazy?** #f)))
          (try (lambda (x) 
                 'done)))
      (lambda () 
        (set! **lazy?** #t)
        (try (unset-lazy)) 
        **lazy?**))))

