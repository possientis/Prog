; example of clojure managed reference ref (see alter and commute also)
; major drawback of ref: in practice, you need to do read-process-write
; Even if you are dealing with immutable object (which guarantees that
; you always read a consistent state), even if you can process a data
; structure locally (creating new immutable object from existing 
; immutable object) and even if you can safely update a reference with
; dosync, this does not solve your problem which is that you want:
;
; read - process - write --> should be atomic  --> use 'alter'
;

(def all-users (ref {}))

(println all-users)                       ; #<Ref@36b4fe2a: {}>
(println (deref all-users))               ; {}
(println @all-users)                      ; {}  macro '@' shortcut for 'deref'
(println (:unknown-key @all-users))       ; nil
(println (:unknown-key all-users))        ; nil, still works it seems

;(ref-set all-users {"john" 33})          ; Exception thrown, no transaction running
(dosync (ref-set all-users {"john" 33}))
(println (all-users "john"))              ; 33



