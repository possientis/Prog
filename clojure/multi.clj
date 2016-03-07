; multimethod in action

(defn fee-amount [percentage user]
  (float (* 0.01 percentage (:salary user))))


(defn affiliate-fee-cond [user]
  (cond (= :google.com (:referrer user)) (fee-amount 0.01 user)
        (= :mint.com   (:referrer user)) (fee-amount 0.03 user)
        :default                         (fee-amount 0.02 user)))

;(defmulti name dispatch-fn & option)
; dispatch function is ':referrer' and accepts the same arguments
; (user) as the multimethod being defined. The dispatch function
; return a dispatch value, which will allow to decide at runtime
; on the specific implementation of the multimethod being called
(defmulti affiliate-fee :referrer)  ; so :referrer is the dispatch function

; defining one implementation of multimethod for dispatch value ':mint.com'
(defmethod affiliate-fee :mint.com [user]
  (fee-amount 0.03 user))

; defining another implementation for dispatch value ':google.com
(defmethod affiliate-fee :google.com [user]
  (fee-amount 0.01 user))

; defining yet another implementation, this time for dispatch value ':default
(defmethod affiliate-fee :default [user]  ; use :default, not :else
  (fee-amount 0.02 user))

(def user-1 {:login "rob"   :referrer :mint.com   :salary 100000})
(def user-2 {:login "kyle"  :referrer :google.com :salary 200000})
(def user-3 {:login "dave"  :referrer :yahoo.com  :salary 300000})


(println (affiliate-fee user-1))  ; 30 = 0.03% x 100,000
(println (affiliate-fee user-2))  ; 20 = 0.01% x 200,000 
(println (affiliate-fee user-3))  ; 60 = 0.02% x 300,000

