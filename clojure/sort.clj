(def users [
            {:username "kyle"
             :balance 175.0
             :member-since "2009-04-16"}
            
            {:username "zak"
             :balance 12.95
             :member-since "2009-02-01"}

            {:username "rob"
             :balance 98.50
             :member-since "2009-03-30"}
            ])

(println (map :username users))

(println (map :username (sort-by :balance users)))
(println (sort [2 3 5 1 0 9 3]))
