# Map expressions

Viper has a built-in parametric partial map type `Map[K, V]`, where `K` is a type parameter that describes the type of the keys in the map, and `V` similarly describes the type of the values in the map. Like sets, maps are immutable (i.e., they represent mathematical maps), and they map a finite amount of keys to values.

* empty map: `Map[K, V]()` returns an empty map of type `Map[K, V]`, i.e., a map whose domain is empty. As with empty set literals, the type arguments are optional if the type is clear from the context; then simply `Map()` can be written.

* map literals: `Map(e1 := e2, e3 := e4, ...)` evaluates to a map containing only the explicitly enumerated mappings (i.e, mapping e1 to e2, e3 to e4 etc.), where all keys must have a common type `K` and all values must have a common type `V` s.t. the resulting expression has the type `Map[K, V]`. If multiple key-value pairs have the same key, the map contains the value of the latest such pair. I.e., `Map(1 := 3, 1 := 5)` will contain value 5 for key 1.

* map domain and range: If `m` is a map of type `Map[K, V]`, then `domain(m)` is the finite domain (of type `Set[K]`) of `m`, i.e., the set of keys it contains. Similarly, `range(m)` denotes the range (or image) of `m`, which has type `Set[V]`.

* map cardinality: `|m|` denotes the cardinality of the map `m`, i.e., the cardinality of its domain.  

* map lookup: If `m` is a map of type `Map[K, V]` and `e` has a type `K`, then `m[e]` looks up the value of key `e` in `m`.  As a well-definedness condition, `e` must be known to be in the domain of `m`, otherwise this expression will result in a verification error.

* map membership: `e in m`, where `m` has type `Map[K, V]` and `e` has type `K`, is true iff `e` is in the domain of `m`.

* map update: If `m` is a map of type `Map[K, V]`, `e1` has type `K` and `e2` has type `V`, then `m[e1 := e2]` is a map that is identical to `m` except the key-value-pair `e1 -> e2` has been added (or its value updated).
