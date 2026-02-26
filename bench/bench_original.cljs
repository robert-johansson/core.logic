(ns bench-original
  (:refer-clojure :exclude [==])
  (:require [cljs.core.logic :refer [lvar lcons membero firsto appendo
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
  (all
    (== (list (lvar) (lvar) (list (lvar) (lvar) 'milk (lvar) (lvar)) (lvar) (lvar)) hs)
    (firsto hs (list 'norwegian (lvar) (lvar) (lvar) (lvar)))
    (nexto (list 'norwegian (lvar) (lvar) (lvar) (lvar)) (list (lvar) (lvar) (lvar) (lvar) 'blue) hs)
    (righto (list (lvar) (lvar) (lvar) (lvar) 'ivory) (list (lvar) (lvar) (lvar) (lvar) 'green) hs)
    (membero (list 'englishman (lvar) (lvar) (lvar) 'red) hs)
    (membero (list (lvar) 'kools (lvar) (lvar) 'yellow) hs)
    (membero (list 'spaniard (lvar) (lvar) 'dog (lvar)) hs)
    (membero (list (lvar) (lvar) 'coffee (lvar) 'green) hs)
    (membero (list 'ukrainian (lvar) 'tea (lvar) (lvar)) hs)
    (membero (list (lvar) 'lucky-strikes 'oj (lvar) (lvar)) hs)
    (membero (list 'japanese 'parliaments (lvar) (lvar) (lvar)) hs)
    (membero (list (lvar) 'oldgolds (lvar) 'snails (lvar)) hs)
    (nexto (list (lvar) (lvar) (lvar) 'horse (lvar)) (list (lvar) 'kools (lvar) (lvar) (lvar)) hs)
    (nexto (list (lvar) (lvar) (lvar) 'fox (lvar)) (list (lvar) 'chesterfields (lvar) (lvar) (lvar)) hs)))

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

(println "=== Original CLJS core.logic (compiled) ===")
(run-bench "zebra" #(doall (run-nc 1 [q] (zebrao q))) 50)
(run-bench "appendo-10" bench-appendo 200)
(run-bench "digits-10x10x10" bench-digits 20)
