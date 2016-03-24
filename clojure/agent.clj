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

; send-off
; (send-off the-agent the-function & more-args)


; use send for axctions that are cpu intensive but dont block
; if action blocks, it is a shame coz thread pool has fixed size
(send total-cpu-time + 700) ; fixed thread pool maintained by runtime
(Thread/sleep 1)  ; waiting 1 ms to make sure we see change
(println (deref total-cpu-time))

; the tread pool for send-off can grow in size, so suitable for actions
; which are potentially blocking
(send-off total-cpu-time + 800) ; same as send, but different thread pool
(Thread/sleep 1)  ; waiting 1 ms to make sure we see change
(println (deref total-cpu-time))
;(shutdown-agents) ; needed otherwise, seperate thread lives on 

; await
; (await & the-agents)

(def agent-one (agent 0))
(def agent-two (agent 0))
(def agent-three (agent 0))
(def agent-four (agent 0))

(defn action [value x]
  (send agent-four + x) ; action will itself call another agent
  (+ value x))

(println "first test:")
(send agent-one action 100)
(send agent-two action 200)
(send agent-three action 300)
(await agent-one agent-two agent-three agent-four) ; this will block indefinitely
(println (deref agent-one))
(println (deref agent-two))
(println (deref agent-three))
(println (deref agent-four))

; await-for
; (await-for time-out-in-millis & the-agents)

(println "second test:")
(send agent-one action 100)
(send agent-two action 200)
(send agent-three action 300)
(def x (await-for 1000 agent-one agent-two agent-three agent-four)) ; this has a timeout
(println (deref agent-one))
(println (deref agent-two))
(println (deref agent-three))
(println (deref agent-four))
(println "x = " x)          ; true on succesful completion it seems

(defn bad-action [value]
  (Thread/sleep 1000))

(send agent-one bad-action)       ; thread will never return
(def y (await-for 10 agent-one))  ; 10 ms wait
(println y)                       ; false (time-out was reached)
(println (deref agent-one))      

; errors
(def bad-agent (agent 10))
(println "third test:")
(send bad-agent / 0)                ; agent should fail
(Thread/sleep 250)
;(await-for 10 bad-agent)           ; seems like *this* will throw exception
;(await bad-agent)                  ; this will also throw exception it seems
(println (deref bad-agent))         ; does not throw exception ??
(println (agent-errors bad-agent))  ; (#<ArithmeticException java.lang.ArithmeticException: Divide by zero>)

(clear-agent-errors bad-agent)      ; so you can re-use agent
(println (agent-errors bad-agent))  ; nil


; agent 
; (agent initial-state & options)

; The options allowed are:
; :meta metadata-map (the supplied metadata-map becomes the meta data of agent)
; :validator validator-fn
; If the :validator option is used, it should be accompanied by either nil or
; a function that accepts one argument. The validator-fn is passed the intended new
; state of the agent, and it can apply any business rules in order to allow or disallow the
; change to occur. If the validator function returns false or throws an exception, then
; the state of the agent is not mutated.








(println "shutting down")
(shutdown-agents)



