core.logic (nbb port)
====

A port of [core.logic](https://github.com/clojure/core.logic) for
[nbb](https://github.com/babashka/nbb) (Node.js Babashka), enabling
logic programming from the command line or scripting contexts without
a full ClojureScript compilation step.

This port implements miniKanren-style relational programming as
described in William Byrd's dissertation
[Relational Programming in miniKanren: Techniques, Applications, and Implementations](https://www.proquest.com/docview/304903505/E30282E6EF13453CPQ/1).

Requirements
----

- [nbb](https://github.com/babashka/nbb) (install via `npm install -g nbb`)
- Node.js or [Bun](https://bun.sh) (Bun is ~2x faster for this workload)

Quick start
----

```bash
nbb -cp . -e '
(require (quote [core-logic.nbb :refer [lvar]
                  :refer-macros [run* == fresh conde]]))

(println
  (run* [q]
    (fresh [x y]
      (== x "hello")
      (== y "world")
      (== q [x y]))))
'
```

```
([hello world])
```

Usage
----

Create a `.cljs` file and run it with nbb:

```clojure
;; example.cljs
(ns example
  (:require [core-logic.nbb :as l
             :refer [lvar lcons membero appendo firsto resto
                     conso emptyo nilo succeed fail s# u#]
             :refer-macros [run run* run-nc == fresh conde conda condu
                            all defne matche llist project]]))

(println "Basic unification:")
(println (run* [q] (== q 42)))
;;=> (42)

(println "Appendo:")
(println (run* [q]
           (fresh [x y]
             (appendo x y [1 2 3])
             (== q [x y]))))
;;=> ([() (1 2 3)] [(1) (2 3)] [(1 2) (3)] [(1 2 3) ()])
```

```bash
nbb -cp . example.cljs
```

### Using with Bun

Bun runs nbb workloads roughly 2x faster than Node:

```bash
bun run --bun $(which nbb) -cp . example.cljs
```

### PLDB (fact databases)

A port of `clojure.core.logic.pldb` is included for working with relational databases of facts:

```clojure
(ns example-pldb
  (:require [core-logic.nbb :as l
             :refer-macros [run* == fresh]]
           [core-logic.nbb-pldb :as pldb
             :refer [db-fact db-facts db empty-db]
             :refer-macros [with-db db-rel]]))

(db-rel person name age)

(def people
  (-> empty-db
      (db-fact person "Alice" 30)
      (db-fact person "Bob" 25)
      (db-fact person "Carol" 30)))

(println
  (with-db people
    (run* [name]
      (person name 30))))
;;=> (Alice Carol)
```

Available forms
----

### Core

`run`, `run*`, `run-nc`, `==`, `fresh`, `conde`, `conda`, `condu`, `all`

### Relations

`conso`, `firsto`, `resto`, `membero`, `appendo`, `nilo`, `emptyo`

### Pattern matching

`defne`, `defna`, `defnu`, `matche`, `matcha`, `matchu`, `fne`, `fna`, `fnu`

### Logic constructors

`lvar`, `lcons`, `llist`

### Non-relational

`project`, `pred`, `is`, `lvaro`, `nonlvaro`

### Debugging

`log`, `trace-s`, `trace-lvars`

### Utilities

`succeed` / `s#`, `fail` / `u#`, `unifier`, `binding-map`, `partial-map`

### PLDB (core-logic.nbb-pldb)

`db-rel`, `db-fact`, `db-facts`, `db-retraction`, `db-retractions`, `with-db`, `with-dbs`, `empty-db`

Running the tests
----

```bash
nbb -cp . core_logic/nbb_test.cljs
```

All 129 tests should pass.

Performance
----

The nbb port runs under [SCI](https://github.com/babashka/sci) (Small
Clojure Interpreter), so it is slower than compiled ClojureScript.
Typical overhead is ~10-13x on Bun and ~16-21x on Node compared to
compiled CLJS.

For performance-sensitive workloads, use compiled ClojureScript with
the upstream `org.clojure/core.logic` library.

Limitations
----

This port covers the core miniKanren functionality. The following
JVM-only features are **not included**:

- CLP(FD) finite domain constraints
- Nominal logic programming
- Tabling
- DCG grammars
- Disequality constraints (`!=`) / constraint store

Copyright and license
----

Copyright © David Nolen, Rich Hickey & contributors.

Licensed under the EPL (see the file epl.html).
