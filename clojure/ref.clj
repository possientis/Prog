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

; resetting
(dosync (ref-set all-users {}))
; alter
; (alter ref function & args) .....
; (commute ref function & args ) when order of operation does not matter

(defn new-user [id login monthly-budget]
  {:id id
   :login login
   :monthly-budget monthly-budget
   :total-expenses 0})

; the assoc function
(def x {})
(def y (assoc x :new-key :new-value))
(println y)

; the syncronization with (dosync ... alter ) creates potential
; contention which may be a shame on operations which 'commute',
; i.e. for which you do not need the latest reference state
; (we need to be careful here however, coz of the id generation
; based on count )

(defn add-user [login budget-amount]
  (dosync
    (let [current-number (count @all-users)
          user (new-user (inc current-number) login budget-amount)]
      (alter all-users assoc login user))))

(add-user 'john 10000)
(println all-users)

; creating an agent is similar to creating a ref:
(def total-cpu-time (agent 0))
; dereferencing an agent to get at its value is similar to using a ref:
(println (deref total-cpu-time))  ; 0
(println @total-cpu-time)         ; 0

; mutating an agent is asynchronous and performed by some other thread.
; changes are performed by sending an action (a function) to the agent.
; the action will run on a separate thread.

; send
; (send the-agent the-function & more-args)

; use send for axctions that are cpu intensive but dont block
; if action blocks, it is a shame coz thread pool has fixed size
(send total-cpu-time + 700) ; fixed thread pool maintained by runtime
(Thread/sleep 1)  ; waiting 1 ms to make sure we see change
(println (deref total-cpu-time))
(shutdown-agents) ; needed otherwise, seperate thread lives on


