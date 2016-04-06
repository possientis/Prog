; macro binding dictionary :keys
(defn check-credentials [username password]
  true)

; first attempt: inconvenience of having to explicitely bind all
; the required fields of request
(defn login-user-1 [request]
  (let [username (:username request)
        password (:password request)]
    (if (check-credentials username password)
      (str "Welcome back, " username ", " password " is correct!")
      (str "Login failed!"))))

(def request {:username "amit" :password "123456"})

(println (login-user-1 request))

; second attempt: less verbose , so arguably better. but why not macro it.
(defn login-user-2 [{:keys [username password]}] ; still expects a request as arg
  (if (check-credentials username password)
    (str "Welcome back, " username ", " password " is correct!")
    (str "Login failed!")))

(println (login-user-2 request))

; general solution: macro
(defmacro defwebmethod [name args & exprs]
  `(defn ~name [{:keys ~args}]
     ~@exprs))

; see below for output
(println (str (macroexpand-1 '(defwebmethod login-user-3 [username password]
  (if (check-credentials username password)
      (str "Welcome back, " username ", " password " is correct!")
      (str "Login failed!"))))))

; result of macro expansion (inside comment)
(comment
(defn login-user-3 [{:keys [username password]}] 
  (if (check-credentials username password) 
    (str "Welcome back, " username ", " password " is correct!") 
    (str "Login failed!")))
)

; third attempt: perfect. 
(defwebmethod login-user-3 [username password]
  (if (check-credentials username password)
      (str "Welcome back, " username ", " password " is correct!")
      (str "Login failed!")))

(println (login-user-3 request))


