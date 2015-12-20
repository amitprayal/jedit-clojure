(ns amit.help
  (:import  (java.io File)
  	  		(java.util.zip ZipFile)
  	  		(java.lang.reflect Modifier)
  	  		(java.io BufferedReader File)
		    (clojure.lang LineNumberingPushbackReader)
            (java.io BufferedReader File StringReader)
            (java.lang StringBuilder)
  	  		)
  (:require ;[clj-inspector.jars :as jars]
            ;[clj-inspector.vars :as vars]
            [clojure.pprint :only (pprint)]
            [clojure.zip :as zip])
  (:use [clojure.java.io :only (reader)])
  
  (:gen-class
   :methods [^{:static true} [docs [] void]])
)

(defn present-item [item]
  (str (:name item) " [" (:ns item) "]"))


(def failed-jars (atom []))  

(def failed-to-process (atom []))

(defonce ns-names (atom nil))

(defn has?
  "If x is in collection, returns x, else nil."
  [coll x]
  (some #{x} coll))

(defn read-clojure-source
  "Takes the text of clojure source code and returns a sequence
   of s-expressions with metadata including the line number and
   the source text."
  [text]
  (let [code-reader (LineNumberingPushbackReader.
                      (StringReader. text))
        lines (vec (.split text "\n"))
        total-lines (count lines)]
    (loop [sexprs []]
      (let [sexpr (try (read code-reader) (catch Exception e nil))
            last-line (.getLineNumber code-reader)]
        (if (and sexpr (instance? clojure.lang.IObj sexpr))
          (let [line (:line (meta sexpr))
                sexpr-m
                (vary-meta
                  sexpr merge
                  {:source (.trim (apply str
                                         (interpose "\n"
                                                    (subvec
                                                      lines
                                                      (dec line)
                                                      (min last-line total-lines)))))})]
            (recur (conj sexprs sexpr-m)))
          sexprs)))))
    
;; namespace: { :full-name :short-name :doc :author :members :subspaces :see-also}
;; vars: {:name :doc :arglists :var-type :file :line :added :deprecated :dynamic}

(defn drop-quotes [sexpr]
  (if (and (seq? sexpr)
           (= (first sexpr) 'quote))
    (drop-quotes (second sexpr))
    sexpr))

(defn get-arg-lists [sexpr]
  (let [tail (drop-while #(or (map? %) (string? %)) (drop 2 sexpr))
        exp1 (first tail)]
    (cond (vector? exp1) (list exp1)
          (list? exp1) (map first tail)
          :else nil)))

(defn arglist-expr-to-str [arglist-expr]
  (when arglist-expr
    (pr-str (drop-quotes arglist-expr))))

(defn get-meta-deflike
  [sexpr]
  (meta (second sexpr)))

(defn get-meta-defnlike
  [sexpr]
  (let [[t1 t2 t3 t4] sexpr
        d (if (string? t3) t3)]
    ;(println t2 t3 t4)
    (merge
      (meta t2)
      (if (map? t3) t3)
      (if (and d (map? t4)) t4)
      (if d {:doc d})
      (if (not= t1 'defmulti)
        {:arglists (arglist-expr-to-str (get-arg-lists sexpr))}))))

(defn get-meta-tail-doc
  [sexpr n]
  (merge
    (get-meta-deflike sexpr)
    (let [[_ _ t3 t4] sexpr]
      {:doc
        (str (condp = n
          3 t3
          4 t4))})))

(defn analyze-sexpr
  "Analyze the s-expression for docs and metadata."
  [sexpr]
  (when (seq? sexpr)
    (condp has? (first sexpr)
      '(ns def defhinted defonce defstruct)
      (get-meta-deflike sexpr)
      '(defn definline defmacro defmulti defn-memo defnk)
      (get-meta-defnlike sexpr)
      '(defprotocol defunbound)
      (get-meta-tail-doc sexpr 3)
      '(defalias defvar)
      (get-meta-tail-doc sexpr 4)
      nil)))

(defn get-var-type [sexpr]
    ({'def       "var"
      'defn      "function"
      'definline "function"
      'defmacro  "macro"
      'defmulti  "multimethod"
      'defnmemo  "function"
      'defnk     "function"}
     (first sexpr)))

(defn build-expr-info [sexpr]
  (when (seq? sexpr)
    (let [analysis (analyze-sexpr sexpr)]
      (with-meta
        (if (has? ['ns 'in-ns] (first sexpr))
          (merge
            (select-keys analysis [:doc :author :subspaces :see-also])
            {:full-name (name (drop-quotes (second sexpr)))
             :short-name (name (drop-quotes (second sexpr)))})
          (merge
            (meta sexpr)
            (select-keys analysis [:arglists :doc :added :deprecated :dynamic])
            {:name (try (name (second sexpr)) (catch Exception e nil))
             :var-type (get-var-type sexpr)}))
        {:expr-type (first sexpr)}))))

(defn create-var-entries [sexprs]
  (filter :var-type
          (let [exprs-info (map build-expr-info sexprs)]
            (let [the-ns (first exprs-info)
                  ns-info {:ns (:full-name the-ns)
                           :author (:author the-ns)
                           :ns-doc (:doc the-ns)}]
              (if (has? ['ns 'in-ns] (:expr-type (meta the-ns)))
                (map #(merge ns-info %) (rest exprs-info))
                (throw (Exception. "First element is not a namespace declaration.")))))))

(defn save-names [var-entries]
  (doseq [entry var-entries]
  (swap! ns-names update-in [(:ns entry)] conj (:name entry))))

(defn analyze-clojure-source [source-text]
  ; Important to turn off the EvalReader
  ; because we are reading untrusted code!!!
  (binding [*read-eval* false] 
    (try
      (doto
        (create-var-entries (read-clojure-source source-text))
        save-names)
      (catch Throwable e (do (swap! failed-to-process conj [source-text e]) nil)))))



(defn #^String slurp*
  "Like clojure.core/slurp but opens f with reader."
  [f]
  (with-open [^BufferedReader r (reader f)]
             (let [sb (StringBuilder.)]
               (loop [c (.read r)]
                 (if (neg? c)
                   (str sb)
                   (do (.append sb (char c))
                       (recur (.read r))))))))

(defn jar-files
  "List all jar files located in hierarchy under top-folder."
  [top-folder]
  (->> top-folder
       File.
       file-seq
       (filter #(.endsWith (.getAbsolutePath %) ".jar"))))

(defn get-entries-in-jar
  "Get a list of entries in a jar."
  [file]
  (enumeration-seq (.entries (ZipFile. file))))

(defn slurp-entry [jar-file entry]
  (slurp* (.getInputStream (ZipFile. jar-file) entry)))
       
(defn select-clj-jar-entries
  "Select *.clj files from a list of jar entries."
  [entries]
  (filter #(.endsWith (.getName %) ".clj") entries))

(defn clj-sources-from-jar
  "Read the text of clj source files from a jar file
   and return in a map of path to source text."
  [jar-file]
  (try
    (let [entries (select-clj-jar-entries (get-entries-in-jar jar-file))]
      (into (sorted-map)
            (for [entry entries]
              (let [path (str (.getAbsolutePath jar-file)
                              "!" File/separator
                              (.getName entry))]
                [path
                 (slurp-entry jar-file entry)]))))
    (catch Exception e 
           (do (swap! failed-jars conj [jar-file e]) nil))))



(defn make-var-super-map [var-maps]
  (into {}
        (for [var-map var-maps]
          [[(:ns var-map) (:name var-map)] var-map])))

(defn classpath-to-jars [project-path classpath]
  (apply concat
    (for [item classpath]
      (cond (.endsWith item "*") (jar-files (apply str (butlast item)))
            (.endsWith item ".jar") (list (File. item))
            :else (jar-files item)))))

(defn get-sources-from-jars [project-path classpath]
   (->> (classpath-to-jars project-path classpath)
       (mapcat clj-sources-from-jar)
       merge
       vals))

(defn get-sources-from-clj-files [classpath]
   (prn "get-sources-from-clj-files " classpath )	
  (map slurp
       (apply concat
              (for [item classpath]
                (let [item-file (File. item)]
                  (when (.isDirectory item-file)
                    (filter #(.endsWith (.getName %) ".clj")
                            (file-seq item-file))))))))


(defonce help-state (atom {:visible false :token nil :pos nil}))

(defn var-map [v]
  (when-let [m (meta v)]
    (let [ns (:ns m)]
      (-> m
          (select-keys [:doc :ns :name :arglists])
          (assoc :source (binding [*ns* ns]
                           (clojure.repl/source-fn (symbol (str ns "/" name)))))))))

(defn var-help [var-map]
  (let [{:keys [doc ns name arglists source]} var-map]
    (str name
         (if ns (str " [" ns "]") "") "\n"
         arglists
         "\n\n"
         (if doc
           (str "Documentation:\n" doc)
           "No documentation found.")
         "\n\n"
         (if source
           (str "Source:\n"
                (if doc
                  (.replace source doc "...docs...")
                  source))
           "No source found."))))

(defn create-param-list
  ([method-or-constructor static]
    (str " (["
         (let [type-names (map #(.getSimpleName %)
                               (.getParameterTypes method-or-constructor))
               param-names (if static type-names (cons "this" type-names))]
           (apply str (interpose " " param-names)))
         "])"))
  ([method-or-constructor]
    (create-param-list method-or-constructor true)))

(defn constructor-help [constructor]
  (str (.. constructor getDeclaringClass getSimpleName) "."
       (create-param-list constructor)))

(defn method-help [method]
  (let [stat (Modifier/isStatic (.getModifiers method))]
    (str
      (if stat
        (str (.. method getDeclaringClass getSimpleName)
             "/" (.getName method))
        (str "." (.getName method)))
     (create-param-list method stat)
      " --> " (.getName (.getReturnType method)))))

(defn field-help [field]
  (let [c (.. field getDeclaringClass getSimpleName)]
  (str
    (if (Modifier/isStatic (.getModifiers field))
      (str (.. field getDeclaringClass getSimpleName)
           "/" (.getName field)
           (when (Modifier/isFinal (.getModifiers field))
             (str " --> " (.. field (get nil) toString))))
      (str "." (.getName field) " --> " (.getName (.getType field)))))))

(defn class-help [c]
  (apply str
         (concat
           [(present-item c) "\n  java class"]
           ["\n\nCONSTRUCTORS\n"]
           (interpose "\n"
                      (sort
                        (for [constructor (.getConstructors c)]
                          (constructor-help constructor))))
           ["\n\nMETHODS\n"]
           (interpose "\n"
                      (sort
                        (for [method (.getMethods c)]
                          (method-help method))))
           ["\n\nFIELDS\n"]
           (interpose "\n"
                      (sort
                        (for [field (.getFields c)]
                          (field-help field)))))))


(defn docs [];project-path classpath
  ;
	  (let [
			 cp (.get (System/getProperties) "java.class.path")
			 cpp (.replace cp "\\" "/")
			 paths  (for [ i (.split cpp ";")] i)
			 classpath (filter #(.matches %1 ".*clojure(.*?)\\.jar") paths) 
			 project-path (filter #(and (> (.length %1) 1)  (not (.endsWith %1 ".jar"))) paths)
		   ]
		  (prn 	"docs" project-path classpath)	   
		  (make-var-super-map
			  (mapcat analyze-clojure-source
					  (concat
						(get-sources-from-jars project-path classpath)
						(get-sources-from-clj-files project-path)
					  )
			  )
		  )
	  )
)

(def mdoc nil)

(defn loadhelp[]
	(if (nil? mdoc) (def mdoc (docs)) mdoc  )
)

(defn check-docs [s]
  ;(prn "check-docs " s)
   (loadhelp)
  (let [ v  mdoc
  	     kys  (filter #(.equals (second %1) s) (keys v))
  	     ;res (reduce str "" (for [k kys]  (str k "\n"  (v k))))
  	     res (reduce str "" (for [k kys] (reduce str "" (map #(str ((mdoc k) %1) "\n")  [:ns :name :var-type :arglists :doc]  ) ) ) )
  	   ]
  	   ;(prn res)
  	   ;(.replace (.replace (.replace res "\\n" "\n") "\\t" "\t") "\\r" "\r")
  	   (spit "c:/temp/help.txt" res)
  )
)

;

;(use 'amit.help)
