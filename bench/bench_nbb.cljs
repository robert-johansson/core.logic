(ns bench-nbb
  (:require [core-logic.nbb :as l
             :refer [lvar lcons membero firsto appendo
                     succeed fail s# u# emptyo conso resto]
             :refer-macros [run run* run-nc == fresh conde conda condu
                            all defne matche llist]]))

(defne righto [x y l]
  ([_ _ [x y . r]])
  ([_ _ [_ . r]] (righto x y r)))

(defn nexto [x y l]
  (conde
    [(righto x y l)]
    [(righto y x l)]))

(defn zebrao [hs]
  (let [_ (fn [] (lvar))]
    (all
      (== (list (_) (_) (list (_) (_) 'milk (_) (_)) (_) (_)) hs)
      (firsto hs (list 'norwegian (_) (_) (_) (_)))
      (nexto (list 'norwegian (_) (_) (_) (_)) (list (_) (_) (_) (_) 'blue) hs)
      (righto (list (_) (_) (_) (_) 'ivory) (list (_) (_) (_) (_) 'green) hs)
      (membero (list 'englishman (_) (_) (_) 'red) hs)
      (membero (list (_) 'kools (_) (_) 'yellow) hs)
      (membero (list 'spaniard (_) (_) 'dog (_)) hs)
      (membero (list (_) (_) 'coffee (_) 'green) hs)
      (membero (list 'ukrainian (_) 'tea (_) (_)) hs)
      (membero (list (_) 'lucky-strikes 'oj (_) (_)) hs)
      (membero (list 'japanese 'parliaments (_) (_) (_)) hs)
      (membero (list (_) 'oldgolds (_) 'snails (_)) hs)
      (nexto (list (_) (_) (_) 'horse (_)) (list (_) 'kools (_) (_) (_)) hs)
      (nexto (list (_) (_) (_) 'fox (_)) (list (_) 'chesterfields (_) (_) (_)) hs))))

(defn bench-appendo []
  (count (run* [q]
           (fresh [x y]
             (appendo x y [1 2 3 4 5 6 7 8 9 10])
             (== q [x y])))))

(defn digit-10 [x]
  (conde [(== 0 x)] [(== 1 x)] [(== 2 x)] [(== 3 x)] [(== 4 x)]
         [(== 5 x)] [(== 6 x)] [(== 7 x)] [(== 8 x)] [(== 9 x)]))

(defn bench-digits []
  (count (run* [q]
           (fresh [x y z]
             (digit-10 x) (digit-10 y) (digit-10 z)
             (== q [x y z])))))

(defn run-bench [name f n]
  (println (str "  " name ": warming up..."))
  (dotimes [_ 3] (f))
  (println (str "  " name ": timing " n " iterations..."))
  (let [start (.now js/Date)]
    (dotimes [_ n] (f))
    (let [elapsed (- (.now js/Date) start)]
      (println (str "  " name ": " elapsed "ms (" n " iters, "
                    (.toFixed (/ elapsed n) 2) "ms/iter)")))))

(println "=== nbb port (SCI interpreted) ===")
(run-bench "zebra" #(doall (run-nc 1 [q] (zebrao q))) 50)
(run-bench "appendo-10" bench-appendo 200)
(run-bench "digits-10x10x10" bench-digits 20)
