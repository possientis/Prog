;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-tagged-list)) 
  (begin
    (define included-tagged-list #f)
    (display "loading tagged-list")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (tagged-list? exp tag) (if (pair? exp) (eq? (car exp) tag) #f))

))  ; include guard



