;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-force)) 
  (begin
    (define included-new-force #f)
    (display "loading new-force")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; This is the identity function, hence it doesn't 'do' anything
; However, because it is used as a 'primitive' implementation of
; 'force', it will force the evaluation of its argument.
; This is useful when doing IO under lazy evaluation, where it 
; important to ensure a 'read' is actually carried out before
; a port is closed:
;
; (let ((file (open-file "filename" "r")))
;   (let ((content (read file)))
;     (force content)             ; 'content' and 'file'  no longer thunks
;     (close-port file)           ; it is ok to close port now
;     content))                   ; returning actual content, not thunk

(define (new-force expr) expr)

))  ; include guard
