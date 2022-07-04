(ns replacement.import2.data
  (:require [clojure.core.specs.alpha :as core-specs]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as stest]
            [clojure.string :as string]
            [malli.core :as m]
            [malli.dev.pretty :as pretty]
            [malli.error :as me]
            [malli.impl.util :as miu]
            [malli.generator :as mg]
            [malli.registry :as mr]
            [malli.transform :as mt]
            [malli.util :as mu]
            [replacement.protocol.patched-core-specs]))

(defn even-number-of-forms?
  "Returns true if there are an even number of forms in a binding vector"
  [forms]
  (even? (count forms)))


(defn -map-of-tuples? [x] (or (map? x) (and (seqable? x) (every? (fn [e] (and (vector? e) (= 2 (count e)))) x))))
(def MapOfTuples (m/-collection-schema {:type 'MapOfTuples, :pred -map-of-tuples? :unparse #(into {} %)}))

(def primitives-string-names
  (set/map-invert primitives-classnames))


(def java-primitive-classes
  #{"Float"
    "Integer"
    "Long"
    "Boolean"
    "Character"
    "Double"
    "Byte"
    "Short"})

(mr/set-default-registry! (merge (m/default-schemas)
                                 (mu/schemas)))

(def registry*
  (atom (assoc (merge (m/default-schemas)
                      (mu/schemas))
               ::id uuid?
               ::def-sym [:= 'def]
               ::try-sym [:= 'try]
               ::catch-sym [:= 'catch]
               ::finally-sym [:= 'finally]
               ::reify-sym [:= 'reify]
               ::defn-sym [:or [:= 'defn] [:= 'defn-]]
               ::fn-sym [:= 'fn]
               ::defmacro-sym [:= 'defmacro]
               ::ns-sym [:= 'ns]
               ::dot-sym [:= '.]
               ::loop-sym [:= 'loop]
               ::dotimes-sym [:= 'dotimes]
               ::doseq-sym [:= 'doseq]
               ::for-sym [:= 'for]
               ::with-open-sym [:= 'with-open]
               ::let-sym [:= 'let]
               ::if-let-sym [:= 'if-let]
               ::when-let-sym [:= 'when-let]
               ::when-some-sym [:= 'when-some]
               ::if-some-sym [:= 'if-some]
               ::require-sym [:= 'require]
               ::minimal-string [:and
                                 :string
                                 [:fn #(not (clojure.string/blank? %))]]
               ::var-name :symbol
               ::ns-name ::var-name
               ::type [:orn
                       [:ns ::ns-sym]
                       [:dot ::dot-sym]
                       [:def ::def-sym]
                       [:defn ::defn-sym]
                       [:defmacro ::defmacro-sym]
                       [:reify ::reify-sym]
                       [:let ::let-sym]
                       [:with-open ::with-open-sym]
                       [:loop ::loop-sym]
                       [:dotimes ::dotimes-sym]
                       [:for ::for-sym]
                       [:doseq ::doseq-sym]
                       [:if-let ::if-let-sym]
                       [:when-let ::when-let-sym]
                       [:if-some ::if-some-sym]
                       [:when-some ::when-some-sym]
                       [:require ::require-sym]
                       [:other symbol?]]
               ::keys [:vector ident?]
               ::syms [:vector symbol?]
               ::strs [:vector simple-symbol?]
               ::or [:map-of simple-symbol? any?]
               ::as ::local-name
               ::local-name [:and simple-symbol? [:not [:= '&]]]
               ::ns-keys [:tuple
                          [:and qualified-keyword? [:fn #(-> % name #{"keys" "syms"})]]
                          [:vector simple-symbol?]]
               ::map-binding [:tuple [:ref ::binding-form] :any]
               ::qualified-keys-or-syms
               [:tuple
                [:and :qualified-keyword [:fn #(-> % name #{"keys" "syms"})]]
                [:vector simple-symbol?]]
               ::special-binding [:tuple
                                  [:enum :as :or :keys :syms :strs]
                                  [:orn
                                   [:local-name ::local-name]
                                   [:any any?]]]
               ::map-binding-form  [MapOfTuples
                                    [:orn
                                     [:map-binding ::map-binding]
                                     [:qualified-keys-or-syms ::qualified-keys-or-syms]
                                     [:special-binding ::special-binding]]]
               ::seq-binding-form [:and vector? [:catn
                                                 [:forms [:* [:schema [:ref ::binding-form]]]]
                                                 [:rest-forms [:? [:catn
                                                                   [:ampersand [:= '&]]
                                                                   [:form [:schema [:ref ::binding-form]]]]]]
                                                 [:as-form [:? [:catn
                                                                [:as [:= :as]]
                                                                [:as-sym ::local-name]]]]]]
               ::binding-form [:orn
                               [:local-symbol ::local-name]
                               [:seq-destructure ::seq-binding-form]
                               [:map-destructure ::map-binding-form]]
               ::binding [:catn
                          [:form ::binding-form]
                          [:init-expr [:schema [:ref ::form]]]]
               ::bindings [:and
                           [:fn even-number-of-forms?]
                           vector?
                           [:* ::binding]]
               ::loop-form
               [:catn
                [:loop ::loop-sym]
                [:loop-args [:catn
                             [:bindings ::bindings]
                             [:body [:* [:schema [:ref ::form]]]]]]]

               ::dotimes-form
               [:catn
                [:dotimes ::dotimes-sym]
                [:dotimes-args [:catn
                                [:bindings ::bindings]
                                [:body [:* [:schema [:ref ::form]]]]]]]

               ::for-form
               [:catn
                [:for ::for-sym]
                [:for-args [:catn
                            [:bindings ::bindings]
                            [:body [:* [:schema [:ref ::form]]]]]]]

               ::doseq-form
               [:catn
                [:doseq ::doseq-sym]
                [:doseq-args [:catn
                              [:bindings ::bindings]
                              [:body [:* [:schema [:ref ::form]]]]]]]

               ::with-open-form
               [:catn
                [:with-open ::with-open-sym]
                [:with-open-args [:catn
                                  [:bindings ::bindings]
                                  [:body [:* [:schema [:ref ::form]]]]]]]

               ::let-form
               [:catn
                [:let ::let-sym]
                [:let-args [:catn
                            [:bindings ::bindings]
                            [:body [:* [:schema [:ref ::form]]]]]]]

               ::if-let-form
               [:catn
                [:if-let ::if-let-sym]
                [:if-let-args [:catn
                               [:bindings [:and vector? ::binding]]
                               [:then [:schema [:ref ::form]]]
                               [:else [:? [:schema [:ref ::form]]]]]]]

               ::if-some-form
               [:catn
                [:if-some ::if-some-sym]
                [:if-some-args [:catn
                                [:bindings [:and vector? ::binding]]
                                [:then [:schema [:ref ::form]]]
                                [:else [:? [:schema [:ref ::form]]]]]]]

               ::when-let-form
               [:catn
                [:when-let ::when-let-sym]
                [:when-let-args [:catn
                                 [:bindings [:and vector? ::binding]]
                                 [:body [:* [:schema [:ref ::form]]]]]]]

               ::when-some-form
               [:catn
                [:when-some ::when-some-sym]
                [:when-some-args [:catn
                                  [:bindings [:and vector? ::binding]]
                                  [:body [:* [:schema [:ref ::form]]]]]]]

               ::exclude [:sequential simple-symbol?]
               ::only [:sequential simple-symbol?]
               ::rename [:map-of simple-symbol? simple-symbol?]
               ::filters [:map
                          [:exclude {:optional true} ::exclude]
                          [:only {:optional true} ::only]
                          [:rename {:optional true} ::rename]]

               ::ns-refer-clojure
               [:catn
                [:clause [:= :refer-clojure]]
                [:refer-filters ::filters]]

               ::refer
               [:orn
                [:all [:= :all]]
                [:syms [:sequential simple-symbol?]]]

               ::prefix-list
               [:catn
                [:prefix simple-symbol?]
                [:libspecs [:+ ::libspec]]]

               ::as-alias simple-symbol?

               ::libspec
               [:altn
                [:lib simple-symbol?]
                [:lib+opts [:catn
                            [:lib simple-symbol?]
                            [:options [:map
                                       [:as {:optional true} ::as]
                                       [:refer {:optional true} ::refer]
                                       [:as-alias {:optional true} ::as-alias]]]]]]

               ::ns-require
               [:catn
                [:clause [:= :require]]
                [:body [:+ [:altn
                            [:libspec ::libspec]
                            [:prefix-list ::prefix-list]
                            [:flag [:enum :reload :reload-all :verbose]]]]]]

               ::package-list
               [:catn
                [:package simple-symbol?]
                [:classes [:+ simple-symbol?]]]

               ::import-list
               [:* [:altn
                    [:class simple-symbol?]
                    [:package-list ::package-list]]]

               ::ns-import
               [:catn
                [:clause [:= :import]]
                [:classes ::import-list]]

               ::ns-refer
               [:catn
                [:clause [:= :refer]]
                [:lib simple-symbol?]
                [:refer-filters ::filters]]

               ;; same as ::prefix-list, but with ::use-libspec instead
               ::use-prefix-list
               [:catn
                [:prefix simple-symbol?]
                [:libspecs [:+ ::use-libspec]]]

               ;; same as ::libspec, but also supports the ::filters options in the libspec
               ::use-libspec
               [:altn
                [:lib simple-symbol?]
                [:lib+opts [:catn
                            [:lib simple-symbol?]
                            [:options [:map
                                       [:as {:optional true} ::as]
                                       [:refer {:optional true} ::refer]
                                       [:exclude {:optional true} ::exclude]
                                       [:only {:optional true} ::only]
                                       [:rename {:optional true} ::rename]]]]]]

               ::ns-use
               [:catn
                [:clause [:= :use]]
                [:libs [:+ [:altn
                            [:libspec ::use-libspec]
                            [:prefix-list ::use-prefix-list]
                            [:flag [:enum :reload :reload-all :verbose]]]]]]

               ::ns-load
               [:catn
                [:clause [:= :load]]
                [:libs [:* string?]]]

               ::name simple-symbol?
               ::extends simple-symbol?
               ::implements [:vector simple-symbol?]
               ::init symbol?
               ::class-ident
               [:orn
                [:class simple-symbol?]
                [:class-name string?]]

               ::signature [:vector ::class-ident]
               ::constructors [:map-of ::signature ::signature]
               ::post-init symbol?
               ::method [:and
                         vector?
                         [:catn
                          [:method-name simple-symbol?]
                          [:param-types ::signature]
                          [:return-type ::class-ident]]]
               ::methods [:vector ::method]
               ::main boolean?
               ::factory simple-symbol?
               ::state simple-symbol?
               ::get simple-symbol?
               ::set simple-symbol?
               ::expose [:map
                         [:get {:optional true} ::get]
                         [:set {:optional true} ::set]]
               ::exposes [:map-of simple-symbol? ::expose]
               ::prefix string?
               ::impl-ns simple-symbol?
               ::load-impl-ns boolean?

               ::ns-gen-class
               [:catn
                [:clause [:= :gen-class]]
                [:options [:map
                           [:name {:optional true} ::name]
                           [:extends {:optional true} ::extends]
                           [:implements {:optional true} ::implements]
                           [:init {:optional true} ::init]
                           [:constructors {:optional true} ::constructors]
                           [:post-init {:optional true} ::post-init]
                           [:methods {:optional true} ::methods]
                           [:main {:optional true} ::main]
                           [:factory {:optional true} ::factory]
                           [:state {:optional true} ::state]
                           [:exposes {:optional true} ::exposes]
                           [:prefix {:optional true} ::prefix]
                           [:impl-ns {:optional true} ::impl-ns]
                           [:load-impl-ns {:optional true} ::load-impl-ns]]]]

               ::ns-clauses
               [:* [:altn
                    [:refer-clojure ::ns-refer-clojure]
                    [:require ::ns-require]
                    [:import ::ns-import]
                    [:use ::ns-use]
                    [:refer ::ns-refer]
                    [:load ::ns-load]
                    [:gen-class ::ns-gen-class]]]

               ::ns-args
               [:catn
                [:ns-name simple-symbol?]
                [:docstring [:? string?]]
                [:attr-map [:? map?]]
                [:ns-clauses ::ns-clauses]]

               ::ns-form
               [:catn
                [:ns ::ns-sym]
                [:ns-args ::ns-args]]

               ::param-list
               [:and
                vector?
                [:catn
                 [:args [:* ::binding-form]]
                 [:varargs [:? [:catn
                                [:amp [:= '&]]
                                [:form ::binding-form]]]]]]

               ::params+body
               [:catn
                [:params ::param-list]
                [:body [:altn
                        [:prepost+body [:catn
                                        [:prepost map?]
                                        [:body [:+ [:schema [:ref ::form]]]]]]
                        [:body [:* [:schema [:ref ::form]]]]]]]

               ::defn-args
               [:catn
                [:fn-name simple-symbol?]
                [:docstring [:? string?]]
                [:meta [:? map?]]
                [:fn-tail [:altn
                           [:arity-1 ::params+body]
                           [:arity-n [:catn
                                      [:bodies [:+ ::params+body]]
                                      [:attr-map [:? map?]]]]]]]

               ::fn-args
               [:catn
                [:fn-name [:? simple-symbol?]]
                [:docstring [:? string?]]
                [:meta [:? map?]]
                [:fn-tail [:altn
                           [:arity-1 ::params+body]
                           [:arity-n [:catn
                                      [:bodies [:+ ::params+body]]
                                      [:attr-map [:? map?]]]]]]]
               ::defn-form
               [:catn
                [:defn-type ::defn-sym]
                [:defn-args ::defn-args]]

               ::fn-form
               [:catn
                [:defn-type ::fn-sym]
                [:defn-args ::fn-args]]

               ::defmacro-form
               [:catn
                [:defn-type ::defmacro-sym]
                [:defn-args ::defn-args]]

               ::def-form
               [:catn
                [:def ::def-sym]
                [:var-name symbol?]
                [:docstring [:? string?]]
                [:init-expr [:+ any?]]]

               ::protocol-impl
               [:catn
                [:method symbol?]
                [:args ::param-list]
                [:bodies [:* [:schema [:ref ::form]]]]]

               ::reify-form
               [:catn
                [:reify ::reify-sym]
                [:reify-args [:* [:orn
                                  [:protocol symbol?]
                                  [:impl [:* ::protocol-impl]]]]]]

               ::require-form
               [:catn
                [:require ::require-sym]
                [:args [:+ [:altn
                            [:libspec ::libspec]
                            [:prefix-list ::prefix-list]
                            [:flag [:enum :reload :reload-all :verbose]]]]]]

               ::java-call
               [:and list?
                [:catn
                 [:method [:and
                           symbol?
                           ;; need a better discriminator cos this gets called too much
                           [:fn #(class? (some-> (namespace %)
                                                 symbol
                                                 resolve))]]]
                 [:args [:* any?]]]]

               ::java-class
               [:and
                symbol?
                [:fn #(class? %)]]

               ::java-type
               [:and
                symbol?
                [:fn #(primitives-string-names (str %))]]

               ::java-value
               [:and
                symbol?
                [:fn #(some-> % namespace java-primitive-classes)]]

               ;; [ ] (. instance-expr member-symbol)
               ;; [x] (. Classname-symbol member-symbol)
               ;; [ ] (. instance-expr -field-symbol)
               ;; [ ] (. instance-expr (method-symbol args*))
               ;; [ ] (. instance-expr method-symbol args*)
               ;; [x] (. Classname-symbol (method-symbol args*))
               ;; [x] (. Classname-symbol method-symbol args*)

               ::dot-form
               [:catn
                [:dot ::dot-sym]
                [:classname symbol?]
                [:method+args [:altn
                               [:method symbol?]
                               [:method+args [:catn
                                              [:method symbol?]
                                              [:args* [:* [:schema [:ref ::form]]]]]]
                               [:method+args-sexp [:orn
                                                   [:method symbol?]
                                                   [:method+args [:catn
                                                                  [:method symbol?]
                                                                  [:args* [:* [:schema [:ref ::form]]]]]]]]]]]

               ::catch-form
               [:catn
                [:catch ::catch-sym]
                [:handled symbol?]
                [:binding ::binding]
                [:body [:* [:schema [:ref ::form]]]]]

               ::try-catch-form
               [:catn
                [:try ::try-sym]
                [:body [:* [:schema [:ref ::form]]]]
                [:catch* [:+ ::catch-form]]
                [:finally? [:? [:catn
                                [:finally ::finally-sym]
                                [:body [:* [:schema [:ref ::form]]]]]]]]

               ::form
               [:orn
                [:ns ::ns-form]
                [:def ::def-form]
                [:defn ::defn-form]
                [:dot-form ::dot-form]
                [:fn ::fn-form]
                [:reify ::reify-form]
                [:require ::require-form]
                [:java-call ::java-call]
                [:java-class ::java-class]
                [:java-type ::java-type]
                [:try-catch ::try-catch-form]
                [:java-value ::java-value]
                [:defmacro ::defmacro-form]
                [:loop ::loop-form]
                [:dotimes ::dotimes-form]
                [:for ::for-form]
                [:doseq ::doseq-form]
                [:with-open ::with-open-form]
                [:let ::let-form]
                [:if-let ::if-let-form]
                [:when-let-form ::when-let-form]
                [:if-some ::if-some-form]
                [:when-some-form ::when-some-form]
                [:expr [:+ [:schema [:ref ::form]]]]
                [:nil nil?]
                [:any any?]]


               ::conformed [:maybe map?]
               ::explain map?
               ::unformed [:maybe ::form]
               ::form-data [:map
                            [:text ::text]
                            [:conformed ::conformed]
                            [:unformed ::unformed]
                            [:explain {:optional true} ::explain]])))

(defn register! [type ?schema]
  (swap! registry* assoc type ?schema))

(mr/set-default-registry!
 (mr/mutable-registry registry*))

(def form-parser (m/parser ::form))
(def form-unparser (m/unparser ::form))
(def Form (m/schema ::form))
