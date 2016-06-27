(defn new-user [login password email]
  (fn [a]
    (condp = a
      :login login
      :password password
      :email email)))


(def x (new-user "john" "xxx" "john@host"))

(println (x :login))

(defn user [login password email]
  (fn [a]
    (cond (= a :login) login
          (= a :password) password
          (= a :email) email)))

(def y (user "john" "xxx" "john@host"))

(println (y :email))
