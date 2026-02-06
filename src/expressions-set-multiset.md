# Set and multiset expressions

Viper has a built-in parametric finite set type `Set[T]`, where `T` is a type parameter that describes the type of the elements of the set. Sets are immutable (i.e. represent mathematical sets).

* empty set: `Set[T]()` returns an empty set of type `Set[T]`. The type argument `T` is optional if the type is clear from the context; then simply `Set()` can be written.

* set literals: `Set(e1, e2, ..., en)` evaluates to a set containing only the n enumerated values and has the type `Set[T]`, where `T` is the common type of the enumerated expressions.

* `e1 union e2`, `e1 intersection e2`, `e1 setminus e2` perform the respective set operations. In all cases, `e1` and `e2` must be sets of the same type, and the entire expression has the same type as its operands. These operators each define a set; the operand sets will not be modified (Viper sets are immutable).

* `e1 subset e2` has type `Bool` and evaluates to `true` if and only if `e1` is a subset of `e2`. Again, both operands have to be sets of the same type.

* Similarly, `e1 in e2`, where `e2` has the type `Set[T]` for some `T` and `e1` has type `T`, evaluates to true if and only `e1` is a member of `e2`.

* set cardinality `|s|` evaluates to a non-negative integer that represents the cardinality of `s`.

Similar to sets, Viper supports multisets:

* Literals can either be empty multisets (`Multiset[T]()`) or non-empty ones (`Multiset(e, ...)`) and work like their set counterparts.

* As for sets, the operations `union`, `intersection`, `setminus`, `subset` and cardinality `|s|` are supported.

* `e1 in e2`, where `e1` has type `T` and `e2` has type `Multiset[T]`, denotes the multiplicity of `e1` in `e2`. 
