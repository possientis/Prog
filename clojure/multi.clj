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

; the use of '::' seems to be significant
; "The extra colon resolves each of these keywords to
; the namespace it’s used in."
; note use of random generation function
; so the keyword are not going to be :bronze :silver etc
; but :user/bronze :user/silver etc
; namespace qualified keywords
; 
(defn profit-rating [user]
  (let [ratings [::bronze ::silver ::gold ::platinum]]
    (nth ratings (rand-int (count ratings)))))

(println (profit-rating user-1))
(println (profit-rating user-2))
(println (profit-rating user-3))


(defn fee-category [user]
  [(:referrer user) (profit-rating user)])


(println (fee-category user-1))
(println (fee-category user-2))
(println (fee-category user-3))

(defmulti profit-based-affiliate-fee fee-category)
; this is a form of double dispatch
(defmethod profit-based-affiliate-fee [:mint.com ::bronze] [user]
  (fee-amount 0.03 user))
(defmethod profit-based-affiliate-fee [:mint.com ::silver] [user]
  (fee-amount 0.04 user))
(defmethod profit-based-affiliate-fee [:mint.com ::gold] [user]
  (fee-amount 0.05 user))
(defmethod profit-based-affiliate-fee [:mint.com ::platinum] [user]
  (fee-amount 0.05 user))
(defmethod profit-based-affiliate-fee [:google.com ::gold] [user]
  (fee-amount 0.03 user))
(defmethod profit-based-affiliate-fee [:google.com ::platinum] [user]
  (fee-amount 0.03 user))
(defmethod profit-based-affiliate-fee :default [user]
  (fee-amount 0.02 user))



(derive ::bronze ::basic)
(derive ::silver ::basic)
(derive ::gold ::premier)
(derive ::platinum ::premier)


(println (isa? ::platinum ::premier)) ; true
(println (isa? ::premier ::platinum)) ; false
(println (isa? ::xxx ::yyy))          ; false
(println (isa? ::bronze ::premier))   ; false

; now that we have a hierarchy we can redifine the multimethod:
; gold and platinum are premier, so code does the same thing
(defmulti affiliate-fee-for-hierarchy fee-category)
(defmethod affiliate-fee-for-hierarchy [:mint.com ::bronze] [user]
  (fee-amount 0.03 user))
(defmethod affiliate-fee-for-hierarchy [:mint.com ::silver] [user]
  (fee-amount 0.04 user))
(defmethod affiliate-fee-for-hierarchy [:mint.com ::premier] [user]
  (fee-amount 0.05 user))
(defmethod affiliate-fee-for-hierarchy [:google.com ::premier] [user]
  (fee-amount 0.03 user))
(defmethod affiliate-fee-for-hierarchy :default [user]
  (fee-amount 0.02 user))





