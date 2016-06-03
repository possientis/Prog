(ns test_hiccup
  (:gen-class)
  (:require [hiccup.core :as h]))
  



(defn -main []
  (println "test_hiccup is running...")
  (println (h/html "something"))        ; #<RawString something>
  (println (str (h/html "something")))  ; something
  (println (h/html 1))                  ; #<RawString 1>
  (println (str (h/html 1)))            ; 1
  (println (h/html [:div]))             ; #<RawString <div></div>> 
  (println (h/html [:div#topseller]))   ; #<RawString <div id="topseller"></div>>
  (println (h/html [:div.product]))     ; #<RawString <div class="product"></div>>
  ; #<RawString <div class="product" id="topseller"></div>>
  (println (h/html [:div#topseller.product]))
  ; #<RawString <div class="product" id="topseller" runa_type="product"></div>>
  (println (h/html [:div#topseller.product {:runa_type "product"}]))
  ; #<RawString <div class="product" id="topseller">Baby T-shirt</div>>
  (println (h/html [:div#topseller.product "Baby T-shirt"]))
  ; #<RawString <span><div>Baby T-shirts!</div></span>>
  (println (h/html [:span [:div "Baby T-shirts!"]]))
  ; #<RawString <ul type="romans"><li>iii</li><li>iv</li><li>v</li></ul>>
  (println (h/html [:ul {:type "romans"}
                    (for [char '("iii" "iv" "v")]
                      [:li char])]))
  ; ([:li iii] [:li iv] [:li v])
  (println (for [char '("iii" "iv" "v")] [:li char]))

  ; the optional map argument of the html macro need not be a map literal.

  (defn optional-tags [description price]
    {:desc description :price price})

  ; #<RawString <div class="product" desc="Top seller!" price="19.95">Baby T-Shirt</div>>
  (println (h/html [:div.product (optional-tags "Top seller!" 19.95) "Baby T-Shirt"]))


  ; (h/html [:div#topseller.product {:runa_type product} Baby T-Shirt]) .... hhhmm, no expansion?
  (println (macroexpand '(h/html [:div#topseller.product {:runa_type "product"} "Baby T-Shirt"])))






)
