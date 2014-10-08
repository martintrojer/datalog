;;  Copyright (c) Jeffrey Straszheim. All rights reserved.  The use and
;;  distribution terms for this software are covered by the Eclipse Public
;;  License 1.0 (http://opensource.org/licenses/eclipse-1.0.php) which can
;;  be found in the file epl-v10.html at the root of this distribution.  By
;;  using this software in any fashion, you are agreeing to be bound by the
;;  terms of this license.  You must not remove this notice, or any other,
;;  from this software.
;;
;;  softstrat.clj
;;
;;  A Clojure implementation of Datalog -- Soft Stratification
;;
;;  straszheimjeffrey (gmail)
;;  Created 28 Feburary 2009

;; Converted to Clojure1.4 by Martin Trojer 2012.

(ns datalog.softstrat
  (:require
   [clojure.set :as set]
   [datalog.database :as database]
   [datalog.graph :as graph]
   [datalog.literals :as literals]
   [datalog.magic :as magic]
   [datalog.rules :as rules]
   [datalog.util :as util]))

;; =============================
;; Dependency graph

(defn- build-rules-graph
  "Given a rules-set (rs), build a graph where each predicate symbol in rs,
  there is a node n, and for each rule (<- h b-1 b-2 ...), there are edges
  from the (literal-predicate h) -> (literal-predicate b-*), one for each
  b-*."
  [rs]
  (let [preds (rules/all-predicates rs)
        pred-map (rules/predicate-map rs)
        step (fn [nbs pred]
               (let [rules (pred-map pred)
                     preds (reduce (fn [pds lits]
                                     (reduce (fn [pds lit]
                                               (if-let [pred (literals/literal-predicate lit)]
                                                 (conj pds pred)
                                                 pds))
                                             pds
                                             lits))
                                   #{}
                                   (map :body rules))]
                 (assoc nbs pred preds)))
        neighbors (reduce step {} preds)]
    (graph/->DirectedGraph preds neighbors)))

(defn- build-def
  "Given a rules-set, build its def function"
  [rs]
  (let [pred-map (rules/predicate-map rs)
        graph (-> rs
                  build-rules-graph
                  graph/transitive-closure
                  graph/add-loops)]
    (fn [pred]
      (apply set/union (map set (map pred-map (graph/get-neighbors graph pred)))))))

;; =============================
;; Soft Stratificattion REQ Graph                 

(defn- req
  "Returns a rules-set that is a superset of req(lit) for the lit at
  index lit-index"
  [rs soft-def rule lit-index]
  (let [head (:head rule)
        body (:body rule)
        lit (nth body lit-index)
        pre (subvec (vec body) 0 lit-index)]
    (conj (-> lit literals/literal-predicate soft-def (magic/magic-transform (rules/all-predicates rs)))
          (rules/build-rule (literals/magic-literal lit) pre))))

(defn- rule-dep
  "Given a rule, return the set of rules it depends on."
  [rs mrs soft-def rule]
  (let [step (fn [nrs [idx lit]]
               (if (literals/negated? lit)
                 (set/union nrs (req rs soft-def rule idx))
                 nrs))]
    (set/intersection mrs
                  (reduce step rules/empty-rules-set
                          (->> rule :body (map-indexed vector))))))

(defn- soft-strat-graph
  "The dependency graph for soft stratification."
  [rs mrs]
  (let [soft-def (build-def rs)
        step (fn [nbrs rule]
               (assoc nbrs rule (rule-dep rs mrs soft-def rule)))
        nbrs (reduce step {} mrs)]
    (graph/->DirectedGraph mrs nbrs)))

(defn- build-soft-strat
  "Given a rules-set (unadorned) and an adorned query, return the soft
  stratified list.  The rules will be magic transformed, and the
  magic seed will be appended."
  [rs q]
  (let [ars (magic/adorn-rules-set rs q)
        mrs (conj (magic/magic-transform ars)
                  (magic/seed-rule q))
        gr (soft-strat-graph ars mrs)]
    (map rules/make-rules-set (graph/dependency-list gr))))

;; =============================
;; Work plan

(defrecord SoftStratWorkPlan [query stratification])

(defn build-soft-strat-work-plan
  "Return a work plan for the given rules-set and query"
  [rs q]
  (let [aq (magic/adorn-query q)]
    (->SoftStratWorkPlan aq (build-soft-strat rs aq))))

(defn get-all-relations
  "Return a set of all relation names defined in this workplan"
  [ws]
  (apply set/union (map rules/all-predicates (:stratification ws))))

;; =============================
;; Evaluate

(defn- weak-consq-operator
  [db strat]
  (util/trace-datalog (println)
                      (println)
                      (println "=============== Begin iteration ==============="))
  (let [counts (database/database-counts db)]
    (loop [strat strat]
      (let [rs (first strat)]
        (if rs
          (let [new-db (rules/apply-rules-set db rs)]
            (if (= counts (database/database-counts new-db))
              (recur (next strat))
              new-db))
          db)))))

(defn evaluate-soft-work-set
  ([ws db] (evaluate-soft-work-set ws db {}))
  ([ws db bindings]
     (let [query (:query ws)
           strat (:stratification ws)
           seed (magic/seed-predicate-for-insertion query)
           seeded-db (literals/project-literal db seed [bindings] util/is-query-var?)
           fun (fn [data]
                 (weak-consq-operator data strat))
           equal (fn [db1 db2]
                   (= (database/database-counts db1) (database/database-counts db2)))
           new-db (graph/fixed-point seeded-db fun nil equal)
           pt (magic/build-partial-tuple query bindings)]
       (database/select new-db (literals/literal-predicate query) pt))))
