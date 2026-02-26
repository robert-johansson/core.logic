(ns core-logic.nbb-test
  (:require [core-logic.nbb :as l
             :refer [lvar lcons -unify -ext-no-check -walk -walk*
                     -reify-lvar-name empty-s to-s succeed fail s# u# conso
                     nilo firsto resto emptyo appendo membero
                     unifier binding-map partial-map failed? lvar?
                     choice take* mplus bind lcons?]
             :refer-macros [run run* run-nc == conde conda condu fresh defne
                            defna defnu matche matcha matchu all llist log
                            trace-s trace-lvars project pred lvaro nonlvaro]]
           [core-logic.nbb-pldb :as pldb
             :refer [db-fact db-retraction db-facts db db-retractions
                     empty-db]
             :refer-macros [with-db with-dbs db-rel]]))

(def test-count (atom 0))
(def fail-count (atom 0))

(defn check [actual expected msg]
  (swap! test-count inc)
  (if (= actual expected)
    (println "  PASS:" msg)
    (do
      (swap! fail-count inc)
      (println "  FAIL:" msg)
      (println "    expected:" (pr-str expected))
      (println "    actual:  " (pr-str actual)))))

(defn testing [name f]
  (println (str "\n" name))
  (f))

;; =============================================================================
;; Unify with nil

(testing "Unify with nil"
  (fn []
    (check (failed? (-unify empty-s nil 1)) true "nil != 1")
    (let [x (lvar 'x)
          a (-ext-no-check empty-s x nil)
          b (-unify empty-s nil x)]
      (check (= a b) true "nil unifies with lvar"))
    (let [x (lvar 'x)]
      (check (failed? (-unify empty-s nil (lcons 1 x))) true "nil != lcons"))
    (check (failed? (-unify empty-s nil {})) true "nil != {}")
    (check (failed? (-unify empty-s nil #{})) true "nil != #{}")))

;; =============================================================================
;; Unify with object

(testing "Unify with object"
  (fn []
    (check (failed? (-unify empty-s 1 nil)) true "1 != nil")
    (check (= (-unify empty-s 1 1) empty-s) true "1 == 1")
    (check (= (-unify empty-s :foo :foo) empty-s) true ":foo == :foo")
    (check (= (-unify empty-s 'foo 'foo) empty-s) true "'foo == 'foo")
    (check (= (-unify empty-s "foo" "foo") empty-s) true "\"foo\" == \"foo\"")
    (check (failed? (-unify empty-s 1 2)) true "1 != 2")
    (check (failed? (-unify empty-s :foo :bar)) true ":foo != :bar")
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x 1)]
      (check (= (-unify empty-s 1 x) os) true "1 unifies with lvar"))
    (check (failed? (-unify empty-s 1 '())) true "1 != '()")
    (check (failed? (-unify empty-s 1 '[])) true "1 != []")
    (check (failed? (-unify empty-s 1 {})) true "1 != {}")
    (check (failed? (-unify empty-s 1 #{})) true "1 != #{}")))

;; =============================================================================
;; Unify with lvar

(testing "Unify with lvar"
  (fn []
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x 1)]
      (check (= (-unify empty-s x 1) os) true "lvar unifies with 1"))
    (let [x (lvar 'x)
          y (lvar 'y)
          os (-ext-no-check empty-s x y)]
      (check (= (-unify empty-s x y) os) true "lvar unifies with lvar"))
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x [])]
      (check (= (-unify empty-s x []) os) true "lvar unifies with []"))
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x [1 2 3])]
      (check (= (-unify empty-s x [1 2 3]) os) true "lvar unifies with [1 2 3]"))
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x '())]
      (check (= (-unify empty-s x '()) os) true "lvar unifies with '()"))
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x {})]
      (check (= (-unify empty-s x {}) os) true "lvar unifies with {}"))
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x {1 2 3 4})]
      (check (= (-unify empty-s x {1 2 3 4}) os) true "lvar unifies with map"))))

;; =============================================================================
;; Unify with lcons

(testing "Unify with lcons"
  (fn []
    (let [x (lvar 'x)]
      (check (failed? (-unify empty-s (lcons 1 x) 1)) true "lcons != 1"))
    (let [x (lvar 'x)
          y (lvar 'y)
          lc1 (lcons 1 x)
          lc2 (lcons 1 y)
          os (-ext-no-check empty-s x y)]
      (check (= (-unify empty-s lc1 lc2) os) true "lcons unifies with lcons"))
    (let [x (lvar 'x)
          lc1 (lcons 1 (lcons 2 x))
          l1 '(1 2 3 4)
          os (-ext-no-check empty-s x '(3 4))]
      (check (= (-unify empty-s lc1 l1) os) true "lcons unifies with list"))
    (let [x (lvar 'x)
          lc1 (lcons 1 (lcons 2 (lcons 3 x)))
          l1 '(1 2 3)
          os (-ext-no-check empty-s x '())]
      (check (= (-unify empty-s lc1 l1) os) true "lcons unifies with exact-length list"))
    (let [x (lvar 'x)
          lc1 (lcons 1 (lcons 3 x))
          l1 '(1 2 3 4)]
      (check (failed? (-unify empty-s lc1 l1)) true "lcons fails on mismatch"))
    (check (failed? (-unify empty-s (lcons 1 (lvar 'x)) {})) true "lcons != {}")
    (check (failed? (-unify empty-s (lcons 1 (lvar 'x)) #{})) true "lcons != #{}")))

;; =============================================================================
;; Unify with sequential

(testing "Unify with sequential"
  (fn []
    (check (failed? (-unify empty-s '() 1)) true "'() != 1")
    (check (failed? (-unify empty-s [] 1)) true "[] != 1")
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x [])]
      (check (= (-unify empty-s [] x) os) true "[] unifies with lvar"))
    (check (= (-unify empty-s [1 2 3] [1 2 3]) empty-s) true "[1 2 3] == [1 2 3]")
    (check (= (-unify empty-s '(1 2 3) [1 2 3]) empty-s) true "'(1 2 3) == [1 2 3]")
    (check (= (-unify empty-s '(1 2 3) '(1 2 3)) empty-s) true "'(1 2 3) == '(1 2 3)")
    (check (failed? (-unify empty-s [1 2] [1 2 3])) true "[1 2] != [1 2 3]")
    (check (failed? (-unify empty-s [1 2 3] [3 2 1])) true "[1 2 3] != [3 2 1]")
    (check (= (-unify empty-s '() '()) empty-s) true "'() == '()")
    (check (failed? (-unify empty-s '() '(1))) true "'() != '(1)")
    (check (= (-unify empty-s [[1 2]] [[1 2]]) empty-s) true "nested vectors")
    (check (failed? (-unify empty-s [[1 2]] [[2 1]])) true "nested vectors mismatch")
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x 1)]
      (check (= (-unify empty-s [[x 2]] [[1 2]]) os) true "lvar in nested vec"))
    (check (failed? (-unify empty-s [] {})) true "[] != {}")
    (check (failed? (-unify empty-s '() {})) true "'() != {}")))

;; =============================================================================
;; Unify with map

(testing "Unify with map"
  (fn []
    (check (failed? (-unify empty-s {} 1)) true "{} != 1")
    (let [x (lvar 'x)
          os (-ext-no-check empty-s x {})]
      (check (= (-unify empty-s {} x) os) true "{} unifies with lvar"))
    (check (= (-unify empty-s {} {}) empty-s) true "{} == {}")
    (check (= (-unify empty-s {1 2 3 4} {1 2 3 4}) empty-s) true "maps equal")
    (check (failed? (-unify empty-s {1 2} {1 2 3 4})) true "maps diff size")
    (let [x (lvar 'x)
          m1 {1 2 3 4}
          m2 {1 2 3 x}
          os (-ext-no-check empty-s x 4)]
      (check (= (-unify empty-s m1 m2) os) true "map with lvar val"))
    (let [x (lvar 'x)
          m1 {1 2 3 4}
          m2 {1 4 3 x}]
      (check (failed? (-unify empty-s m1 m2)) true "map val mismatch"))))

;; =============================================================================
;; Walk

(testing "Walk"
  (fn []
    (let [x (lvar 'x)
          y (lvar 'y)
          s (to-s [[x 5] [y x]])]
      (check (= (-walk s y) 5) true "walk follows chain"))
    (let [[x y z c b a] (map lvar '[x y z c b a])
          s (to-s [[x 5] [y x] [z y] [c z] [b c] [a b]])]
      (check (= (-walk s a) 5) true "walk follows long chain"))))

;; =============================================================================
;; Walk*

(testing "Walk*"
  (fn []
    (let [x (lvar 'x)
          y (lvar 'y)]
      (check (= (-walk* (to-s [[x 5] [y x]]) `(~x ~y))
             '(5 5))
          true "walk* resolves in list"))))

;; =============================================================================
;; run and unify

(testing "run and unify"
  (fn []
    (check (= (run* [q] (== true q))
           '(true))
        true "run* == true")

    (check (= (run* [q]
             (fresh [x y]
               (== [x y] [1 5])
               (== [x y] q)))
           [[1 5]])
        true "run* fresh with vectors")

    (check (= (run* [q]
             (fresh [x y]
               (== [x y] q)))
           '[[_.0 _.1]])
        true "run* with unbound vars")))

;; =============================================================================
;; fail

(testing "fail goal"
  (fn []
    (check (= (run* [q]
             fail
             (== true q))
           [])
        true "fail prevents results")))

;; =============================================================================
;; Basic

(testing "Basic all"
  (fn []
    (check (= (run* [q]
             (all
               (== 1 1)
               (== q true)))
           '(true))
        true "all conjoins goals")))

;; =============================================================================
;; TRS helper relations

(defn pairo [p]
  (fresh [a d]
    (== (lcons a d) p)))

(defn twino [p]
  (fresh [x]
    (conso x x p)))

(defn listo [l]
  (conde
    [(emptyo l) s#]
    [(pairo l)
     (fresh [d]
       (resto l d)
       (listo d))]))

(defn flatteno [s out]
  (conde
    [(emptyo s) (== '() out)]
    [(pairo s)
     (fresh [a d res-a res-d]
       (conso a d s)
       (flatteno a res-a)
       (flatteno d res-d)
       (appendo res-a res-d out))]
    [(conso s '() out)]))

(defn rembero [x l out]
  (conde
    [(== '() l) (== '() out)]
    [(fresh [a d]
       (conso a d l)
       (== x a)
       (== d out))]
    [(fresh [a d res]
       (conso a d l)
       (conso a res out)
       (rembero x d res))]))

;; =============================================================================
;; conde

(testing "conde"
  (fn []
    (check (= (run* [x]
             (conde
               [(== x 'olive) succeed]
               [succeed succeed]
               [(== x 'oil) succeed]))
           '[olive _.0 oil])
        true "conde interleaves")

    (check (= (run* [r]
             (fresh [x y]
               (conde
                 [(== 'split x) (== 'pea y)]
                 [(== 'navy x) (== 'bean y)])
               (== (cons x (cons y ())) r)))
           '[(split pea) (navy bean)])
        true "conde with fresh")))

(defn teacupo [x]
  (conde
    [(== 'tea x) s#]
    [(== 'cup x) s#]))

(testing "conde with teacupo"
  (fn []
    (check (= (run* [r]
             (fresh [x y]
               (conde
                 [(teacupo x) (== true y) s#]
                 [(== false x) (== true y)])
               (== (cons x (cons y ())) r)))
           '((false true) (tea true) (cup true)))
        true "teacupo interleaving")))

;; =============================================================================
;; conso

(testing "conso"
  (fn []
    (check (= (run* [q]
             (fresh [a d]
               (conso a d ())
               (== (cons a d) q)))
           [])
        true "conso with () fails")

    (check (= (run* [q]
             (conso 'a nil q))
           '[(a)])
        true "conso a nil")

    (check (= (run* [q]
             (conso 'a '(d) q))
           '[(a d)])
        true "conso a (d)")

    (check (= (run* [q]
             (conso 'a q '(a)))
           '[()])
        true "conso rest of (a)")

    (check (= (run* [q]
             (conso q '(b c) '(a b c)))
           '[a])
        true "conso first of (a b c)")))

;; =============================================================================
;; firsto

(testing "firsto"
  (fn []
    (let [result (run* [q] (firsto q '(1 2)))]
      (check (= (count result) 1) true "firsto returns one result")
      ;; The result should be an lcons with (1 2) as first and a fresh lvar as rest
      (let [v (first result)]
        (check (lcons? v) true "firsto result is lcons")))))

;; =============================================================================
;; resto

(testing "resto"
  (fn []
    (check (= (run* [q]
             (resto q '(1 2)))
           '[(_.0 1 2)])
        true "resto with fresh q")

    (check (= (run* [q]
             (resto q [1 2]))
           '[(_.0 1 2)])
        true "resto with vector")

    (check (= (run* [q]
             (resto [1 2] q))
           '[(2)])
        true "resto of [1 2]")

    (check (= (run* [q]
             (resto [1 2 3 4 5 6 7 8] q))
           '[(2 3 4 5 6 7 8)])
        true "resto of long vec")))

;; =============================================================================
;; flatteno

(testing "flatteno"
  (fn []
    (check (= (run* [x]
             (flatteno '[[a b] c] x))
           '(([[a b] c]) ([a b] (c)) ([a b] c) ([a b] c ())
             (a (b) (c)) (a (b) c) (a (b) c ()) (a b (c))
             (a b () (c)) (a b c) (a b c ()) (a b () c)
             (a b () c ())))
        true "flatteno")))

;; =============================================================================
;; membero

(testing "membero"
  (fn []
    (check (= (run* [q]
             (all
               (== q [(lvar)])
               (membero ['foo (lvar)] q)
               (membero [(lvar) 'bar] q)))
           '([[foo bar]]))
        true "membero intersection")))

;; =============================================================================
;; rembero

(testing "rembero"
  (fn []
    (check (= (run 1 [q]
             (rembero 'b '(a b c b d) q))
           '((a c b d)))
        true "rembero")))

;; =============================================================================
;; conde clause count

(defn digit-1 [x]
  (conde
    [(== 0 x)]))

(defn digit-4 [x]
  (conde
    [(== 0 x)]
    [(== 1 x)]
    [(== 2 x)]
    [(== 3 x)]))

(testing "conde clause count"
  (fn []
    (check (= (run* [q]
             (fresh [x y]
               (digit-1 x)
               (digit-1 y)
               (== q [x y])))
           '([0 0]))
        true "1x1 digit")

    (check (= (run* [q]
             (fresh [x y]
               (digit-4 x)
               (digit-4 y)
               (== q [x y])))
           '([0 0] [0 1] [0 2] [1 0] [0 3] [1 1] [1 2] [2 0]
             [1 3] [2 1] [3 0] [2 2] [3 1] [2 3] [3 2] [3 3]))
        true "4x4 digit")))

;; =============================================================================
;; anyo

(defn anyo [q]
  (conde
    [q s#]
    [(anyo q)]))

(testing "anyo"
  (fn []
    (check (= (run 1 [q]
             (anyo s#)
             (== true q))
           (list true))
        true "anyo 1")

    (check (= (run 5 [q]
             (anyo s#)
             (== true q))
           (list true true true true true))
        true "anyo 5")))

;; =============================================================================
;; divergence

(def f1 (fresh [] f1))

(testing "divergence"
  (fn []
    (check (= (run 1 [q]
             (conde
               [f1]
               [(== false false)]))
           '(_.0))
        true "divergence with conde")

    (check (= (run 1 [q]
             (conde
               [f1 (== false false)]
               [(== false false)]))
           '(_.0))
        true "divergence with conde 2")))

(def f2
  (fresh []
    (conde
      [f2 (conde
            [f2]
            [(== false false)])]
      [(== false false)])))

(testing "divergence 2"
  (fn []
    (check (= (run 5 [q] f2)
           '(_.0 _.0 _.0 _.0 _.0))
        true "f2 divergence")))

;; =============================================================================
;; conda (soft-cut)

(testing "conda"
  (fn []
    (check (= (run* [x]
             (conda
               [(== 'olive x) s#]
               [(== 'oil x) s#]
               [u#]))
           '(olive))
        true "conda basic")

    (check (= (run* [x]
             (conda
               [(== 'virgin x) u#]
               [(== 'olive x) s#]
               [(== 'oil x) s#]
               [u#]))
           '())
        true "conda fail on first match")

    (check (= (run* [x]
             (fresh (x y)
               (== 'split x)
               (== 'pea y)
               (conda
                 [(== 'split x) (== x y)]
                 [s#]))
             (== true x))
           '())
        true "conda soft cut")

    (check (= (run* [x]
             (fresh (x y)
               (== 'split x)
               (== 'pea y)
               (conda
                 [(== x y) (== 'split x)]
                 [s#]))
             (== true x))
           '(true))
        true "conda soft cut 2")))

(defn not-pastao [x]
  (conda
    [(== 'pasta x) u#]
    [s#]))

(testing "conda not-pastao"
  (fn []
    (check (= (run* [x]
             (conda
               [(not-pastao x)]
               [(== 'spaghetti x)]))
           '(spaghetti))
        true "conda not-pastao")))

;; =============================================================================
;; condu (committed-choice)

(defn onceo [g]
  (condu
    (g s#)))

(testing "condu"
  (fn []
    (check (= (run* [x]
             (onceo (teacupo x)))
           '(tea))
        true "onceo")

    (check (= (run* [r]
             (conde
               [(teacupo r) s#]
               [(== false r) s#]))
           '(false tea cup))
        true "conde teacupo")

    (check (= (run* [r]
             (conda
               [(teacupo r) s#]
               [(== false r) s#]))
           '(tea cup))
        true "conda teacupo")))

;; =============================================================================
;; nil in collection

(testing "nil in collection"
  (fn []
    (check (= (run* [q] (== q [nil]))
           '([nil]))
        true "nil in vec")

    (check (= (run* [q] (== q [1 nil]))
           '([1 nil]))
        true "[1 nil]")

    (check (= (run* [q] (== q [nil 1]))
           '([nil 1]))
        true "[nil 1]")

    (check (= (run* [q] (== q '(nil)))
           '((nil)))
        true "'(nil)")

    (check (= (run* [q] (== q {:foo nil}))
           '({:foo nil}))
        true "{:foo nil}")

    (check (= (run* [q] (== q {nil :foo}))
           '({nil :foo}))
        true "{nil :foo}")))

;; =============================================================================
;; Unifier

(testing "Unifier"
  (fn []
    (check (= (unifier '(?x ?y) '(1 2))
           '(1 2))
        true "unifier 1")

    (check (= (unifier '(?x ?y 3) '(1 2 ?z))
           '(1 2 3))
        true "unifier 2")

    (check (= (unifier '[(?x . ?y) 3] [[1 2] 3])
           '[(1 2) 3])
        true "unifier 3")

    (check (= (unifier '(?x 2 . ?y) '(1 2 3 4 5))
           '(1 2 3 4 5))
        true "unifier 5")

    (check (= (unifier '(?x 2 . ?y) '(1 9 3 4 5))
           nil)
        true "unifier 6")

    (check (= (binding-map '(?x ?y) '(1 2))
           '{?x 1 ?y 2})
        true "binding-map 1")

    (check (= (binding-map '(?x ?y 3) '(1 2 ?z))
           '{?x 1 ?y 2 ?z 3})
        true "binding-map 2")

    (check (= (binding-map '(?x 2 . ?y) '(1 2 3 4 5))
           '{?x 1 ?y (3 4 5)})
        true "binding-map 5")

    (check (= (binding-map '(?x 2 . ?y) '(1 9 3 4 5))
           nil)
        true "binding-map 6")))

;; =============================================================================
;; Occurs check

(testing "Occurs check"
  (fn []
    (check (= (run* [q]
             (== q [q]))
           ())
        true "occurs check prevents circular")))

;; =============================================================================
;; Unifications that should fail

(testing "Failing unifications"
  (fn []
    (check (= (run* [p]
             (fresh [a b]
               (== b ())
               (== '(0 1) (lcons a b))
               (== p [a b])))
           ())
        true "lcons length mismatch")

    (check (= (run* [p]
             (fresh [a b]
               (== b '(1))
               (== '(0) (lcons a b))
               (== p [a b])))
           ())
        true "lcons value mismatch")

    (check (= (run* [p]
             (fresh [a b c d]
               (== () b)
               (== '(1) d)
               (== (lcons a b) (lcons c d))
               (== p [a b c d])))
           ())
        true "lcons structural mismatch")))

;; =============================================================================
;; Pattern matching - defne

(defne match-map [m o]
  ([{:foo {:bar o}} _]))

(testing "defne"
  (fn []
    (check (= (run* [q]
             (match-map {:foo {:bar 1}} q))
           '(1))
        true "defne map pattern")

    ;; matche test
    (let [map-geto (fn map-geto [m k v]
                     (matche [m]
                       ([[[k v] . _]])
                       ([[_ . tail]] (map-geto tail k v))))]
      (check (= (run* [q] (map-geto (seq {:title "Blub"}) :title q))
             '("Blub"))
          true "matche"))))

;; =============================================================================
;; Partial maps

(testing "Partial maps"
  (fn []
    (check (= '({:a 1})
           (run* [q]
             (fresh [pm x]
               (== pm (partial-map {:a x}))
               (== pm {:a 1 :b 2})
               (== pm q))))
        true "partial-map unify")

    (check (= '(1)
           (run* [q]
             (fresh [pm x]
               (== pm (partial-map {:a x}))
               (== pm {:a 1 :b 2})
               (== x q))))
        true "partial-map extract val")))

;; =============================================================================
;; defne with llist patterns (righto)

(defne righto [x y l]
  ([_ _ [x y . r]])
  ([_ _ [_ . r]] (righto x y r)))

(defn nexto [x y l]
  (conde
    [(righto x y l)]
    [(righto y x l)]))

(testing "righto/nexto"
  (fn []
    (let [results (run 10 [q] (nexto 'dog 'cat q))]
      (check (= (count results) 10) true "nexto produces 10 results")
      ;; Check first result: (dog cat . _.0)
      (let [r (first results)]
        (check (lcons? r) true "nexto result is lcons")
        (check (= (l/-lfirst r) 'dog) true "nexto first lfirst is dog")))))

;; =============================================================================
;; pldb

(db-rel man p)
(db-rel woman p)
(db-rel likes p1 p2)
(db-rel fun p)

(def facts0
  (db
    [man 'Bob]
    [man 'John]
    [man 'Ricky]
    [woman 'Mary]
    [woman 'Martha]
    [woman 'Lucy]
    [likes 'Bob 'Mary]
    [likes 'John 'Martha]
    [likes 'Ricky 'Lucy]))

(def facts1
  (-> facts0
    (db-fact fun 'Lucy)))

(testing "pldb"
  (fn []
    (with-db facts0
      (check (= (run* [q]
               (fresh [x y]
                 (likes x y)
                 (fun y)
                 (== q [x y])))
             '())
          true "pldb no fun facts"))

    (with-db facts1
      (check (= (run* [q]
               (fresh [x y]
                 (likes x y)
                 (fun y)
                 (== q [x y])))
             '([Ricky Lucy]))
          true "pldb with fun Lucy"))))

;; =============================================================================
;; Summary

(println (str "\n================================"))
(println (str "Tests: " @test-count ", Failures: " @fail-count))
(println (str "================================"))

(when (pos? @fail-count)
  (throw (js/Error. (str @fail-count " test(s) failed"))))
