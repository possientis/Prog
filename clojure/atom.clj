; atoms are useful when shared mutable state is needed, but without coordination
; with other state


; The difference between an atom and an agent is that
; updates to agents happen asynchronously at some point in the future, whereas atoms
; are updated synchronously (immediately). Atoms differ from refs in that changes to
; atoms are independent from each other and can’t be coordinated so that they either
; all happen or none do.

; similar to creating a ref
(def total-rows (atom 0))
(println total-rows)          ; #<Atom@45ca843: 0>
(println (deref total-rows))  ; 0
(println @total-rows)         ; 0

; There’s an important difference between atoms and refs, in that changes to one atom 
; are independent of changes to other atoms. Therefore, there’s no need to use 
; transactions when attempting to update atoms.

(reset! total-rows 10)        ; reset! : atom with new value
(println @total-rows)         ; 10

; mutation functions should be free of side effects
; because contention between threads may mean it is 
; run several times before it succeeds.


(swap! total-rows + 100)      ; swap! : read-process-write on atom 
(println @total-rows)         ; 110
; (swap! is implemented in terms of compare-and-set! )


; low-level
; (compare-and-set! the-atom old-value new-value)

; semantics of compare-and-set:
; This function atomically sets the value of the atom to the new value **if**
; (and only if) the current value of the atom is equal to the supplied old value
; returns true if succeed, false otherwise

; this allows to do things like read-process-write
; read and old value, process the old value, and only write if value is still
; equal to old value (i.e. it has not been changed by another thread)

; Testing:

(def x (compare-and-set! total-rows 110 200))   ; should succeed 
(println x)             ; true , as expected
(println @total-rows)   ; 200, as expected

(reset! total-rows 100) ; another thread come in, say
(println @total-rows)   ; 100

(def y (compare-and-set! total-rows 200 300))   ; should fail
(println y)             ; false, as expected
(println @total-rows)   ; 100 still since last write failed



