(let [x 0
      y 1]
  (try 
    (/ y x)
    (catch Exception e
      (println (.getMessage e)))))  ; Divide by zero

(defn try-catch [the-try the-catch]
  (try
    (the-try)
    (catch Exception e
      (the-catch e))))

(let [x 0
      y 1]
  (try-catch #(/ y x) #(println (.getMessage %))))

