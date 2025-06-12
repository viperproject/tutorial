# Expressions and Assertions

## Expressions

Viper supports a number of different kinds of expressions, which can be evaluated to a value of one of the types supported in Viper.

The primitive types supported in Viper are booleans (`Bool`), integers (`Int`), permission amounts (`Perm`), denoting real numbers, and references to heap objects (`Ref`). In addition, there are built-in parameterised set (`Set[T]`), multiset (`Multiset[T]`), sequence (`Seq[T]`), and map (`Map[T, U]`) types, and users can define custom types using [domains](#domains).

Evaluating an expression never changes the state of the program, i.e., expression evaluation has no side effects. However, expression evaluation comes with well-definedness conditions for some expressions: evaluating an expression can cause a verification failure if the expression is not well-defined in the current program state; this leads to a verification error. As an example, the expression `x % y` is not well-defined if `y` is equal to zero, and the expression `o.f` is only well-defined if the current method has the permission to read `o.f` (which also implies that `o` is not null).

In the following, we list the different kinds of expressions, remark on their well-definedness conditions (if any) and the value that they evaluate to.

### Expressions of multiple types

* field access `e.f`: to be well-defined, this requires at least some permission to read the field location; returns a value of the type of the field.

* function application `f(...)`: the function can either be a domain function or a top-level, (potentially heap-dependent) function. In the latter case, for a function application to be well-defined the function's precondition must be fulfilled, and in both cases, the argument expressions must be well-defined and have the expected types. Evaluates to a value of the return type of the function. See the respective sections for more information on top-level [functions](#functions) and [domains](#domains).

* typed function application `(f(...) : Type)`: a variant of the above that additionally enforces that the return type of the function application to be the one given in the expression. This is particularly useful with [domains](#domains) with type parameters, for example `(Nil() : List[Bool])`. The parentheses are mandatory.

* local variable and parameter evaluation `x`: read the current value of the named variable or parameter. Note that it is possible to read local variables which have not been assigned to; in this case, the expression will evaluate to an arbitrary value of its type.

* conditional expressions `e1 ? e2 : e3`, where `e1` has type `Bool` and `e2` and `e3` must have the same type; evaluates to `e2` if `e1` is `true`, and otherwise to `e3`. Short-circuiting evaluation is taken into account when checking well-definedness conditions; e.g. `e2` need only be well-defined when `e1` evaluates to true.

* unfolding expressions `unfolding acc(P(...), p) in e`: Requires that the current method has at least the permission amount `p` of the predicate instance `P(...)`. Evaluates `e` in a context where (this amount of) the predicate instance has been temporarily unfolded (i.e., `P` is no longer available, but its contents are).

* old and labelled-old expressions `old(e)` and `old[l](e)`: Evaluates expression `e` in a different (older) version of the heap. In the first case, this is the heap at the start of the current method call; in the second, it is the heap at the position of the label `l`. For the second expression to be well-defined, the label `l` must be in the same method as the old-expression, and must have been encountered by the time the old-expression is evaluated; as a result, old-expressions cannot be used in functions, predicates or preconditions (they also cannot be used in postconditions but for a different reason: they would be meaningless for the caller). It is not supported to refer back to a label inside a loop body from outside of the loop body. Note that old expressions does not affect the value of variable references; `old(x.f)`, for example, evaluates to the value that the field `f` of the object that the variable `x` *currently* points to had at the beginning of the method.

* function results `result`: Can only be used in postconditions of top-level Viper functions, and refers to the result of the function application; it therefore has the type of the return value of the function the postcondition belongs to.

* let expressions `let v == (e1) in e2`: Evaluates `e1`, and subsequently evaluates `e2` in a context where the variable `v` is bound to the value of `e1` (currently, the *parentheses are necessary*). Let expressions are often convenient when one needs to write an expression with many repetitions, or one that concerns several different heaps. For example, if one wishes to evaluate the *argument* of a function call `f(x.f)` in the current state and the function application itself in the current method's old state, this can be expressed by using a let expression as follows: `let y == (x.f) in old(f(y))`.

### Integer expressions

* constants, e.g. `-2`, `1023123909`. Integers in Viper are signed and unbounded.

* unary minus `-e`: Negates the value of `e` if `e` is itself an integer.

* addition, subtraction, multiplication, division, modulo (`e1 + e2`, `e1 - e2`, `e1 * e2`, `e1 / e2`, `e1 % e2`). For all of these, both operands are expected to be integers, and the result will be an integer. These operators are overloaded; similar operators exist returning `Perm`-typed values; Viper will choose the appropriate operator based on the type information available. The only observable ambiguity is for division, since integer division truncates and `Perm`-typed division does not. In ambiguous cases, the alternative syntax `e1 \ e2` can be used to force `Int`-typed division (`Perm`-typed is otherwise the default).

### Boolean expressions

* constants `true` and `false`

* conjunction `e1 && e2`, disjunction `e1 || e2`, implication `e1 ==> e2`. For all cases, both operands are expected to be booleans, and the result will be a boolean. Viper has short-circuiting semantics for these operators, meaning that, for example, in `e1 && e2`, `e2` will only be evaluated if `e1` evaluates to `true`. In particular, this means that `e2` only has to be well-defined if `e1` is true.

* equality `e1 == e2` and inequality `e1 != e2` on all types. Both operands have to be of the same type, and the result is a boolean.

* quantifiers `forall` and `exists`. See the [section on quantifiers](#quantifiers) for more details.

* For-perm quantifiers `forperm x: Ref [x.f] :: e`. This expression serves as a quantifier over all objects for which a permission to the specified field is held by the current method. Inside the expression `e` in the body, the variable `x` points to an object for which a positive amount of permission to `x.f` is held. The entire expression is true if `e` is true for every such object, and false otherwise. As an example, `forperm x: Ref [x.g] :: x.g > 0` is true if and only if, for all objects to whose `g`-fields the current method holds a permission, the value of the `g`-field is positive.

`forperm` expressions are useful for implementing leak checks. For example, by asserting `forperm x: Ref [x.f] :: false` we can check that in the current context we do not hold any permission to the field `f`. Note that `forperm` expressions are evaluated in the current heap, including side-effects caused during `exhale` operations, as illustrated in the following example:

```silver-runnable
field f: Int
method Foo(x: Ref) {
  inhale acc(x.f)
  exhale forperm y: Ref [y.f] :: false // Fails because we have acc(x.f)
  exhale acc(x.f) && forperm y: Ref [y.f] :: false // Succeeds because we do not have acc(x.f) anymore.
}
```

This is useful, for example, for checking that after the method postcondition is exhaled, the method body does not have any permission left which would be leaked.

Forperm expressions may not be used in functions or predicates.

* equivalence or bi-implication `e1 <==> e2`, where both expressions are of type `Bool`, is equivalent to writing `e1 == e2`.

* negation `!e`: Negates the boolean expression `e`.

* integer or perm comparisons `e1 < e2`, `e1 <= e2`, `e1 > e2`, `e1 >= e2` require that the operands are either both of type `Int` or both of type `Perm`, and return a `Bool`.

### Set and multiset expressions

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

### Sequence expressions {#sequences}

Viper's built-in sequence type `Seq[T]` represents immutable finite sequences of elements of type `T`.

* empty sequence: `Seq[T]()` evaluates to an empty sequence of type `Seq[T]`. As with empty set literals, the type argument only has to be stated explicitly if it is not clear from the surrounding context.

* sequence literal: `Seq(e1, e2, ..., en)`, where `e1`-`en` are expressions that all have a common type `T`, represents a sequence of type `Seq[T]` of `n` elements, whose elements are the argument expressions (i.e., the first element is `e1`, the second `e2` etc., and the last is `en`.

* integer sequence literals: `[e1..e2)`, where `e1` and `e2` are `Int`-typed, represent the sequence of integers ranging from `e1` until, but excluding, `e2` (or the empty sequence, if `e2` is less than or equal to `e1`).

* sequence lookup: `s[e]`, where `s` is an expression of type `Seq[T]` for some `T` and `e` is an integer, returns the element at index `e` in the sequence. As a well-definedness condition, `e` must be known to be non-negative and less than the length of `s`, otherwise this expression will result in a verification error.

* sequence concatenation: `e1 ++ e2` results in a new sequence whose elements are the elements of `e1`, followed by those of `e2`.

* sequence update: `s[e1 := e2]`, where `e1` has type `Int`, `s` has type `Seq[T]` for some `T` and `e2` is of type `T`, denotes the sequence that is identical to `s`, except that the element at index `e1` is `e2` (the operation does not change the original sequence's value, but rather defines a new sequence).

* sub-sequence operations: `s[e1..e2]`, where `s` is a sequence and `e1` and `e2` are integers, returns a new sequence that contains the elements of `s` starting from index `e1` until (but not including) index `e2`. The values of `e1` and `e2` need *not* be valid indices for the sequence; for negative `e1` the operator behaves as if `e1` were equal to `0`, for `e1` larger than `|s|` the empty sequence will result (and vice versa for `e2`). Optionally, either the first or the second index can be left out (leading to expressions of the form `s[..e]` and `s[e..]`), in which case only elements at the end or at the beginning of `s` are dropped, respectively.

* sequence length: `|s|` returns the length of a sequence as an integer.

* sequence member check: `e in s` evaluates to true if `e` is in the sequence `s`.

### Map expressions {#maps}

Viper has a built-in parametric partial map type `Map[K, V]`, where `K` is a type parameter that describes the type of the keys in the map, and `V` similarly describes the type of the values in the map. Like sets, maps are immutable (i.e., they represent mathematical maps), and they map a finite amount of keys to values.

* empty map: `Map[K, V]()` returns an empty map of type `Map[K, V]`, i.e., a map whose domain is empty. As with empty set literals, the type arguments are optional if the type is clear from the context; then simply `Map()` can be written.

* map literals: `Map(e1 := e2, e3 := e4, ...)` evaluates to a map containing only the explicitly enumerated mappings (i.e, mapping e1 to e2, e3 to e4 etc.), where all keys must have a common type `K` and all values must have a common type `V` s.t. the resulting expression has the type `Map[K, V]`. If multiple key-value pairs have the same key, the map contains the value of the latest such pair. I.e., `Map(1 := 3, 1 := 5)` will contain value 5 for key 1.

* map domain and range: If `m` is a map of type `Map[K, V]`, then `domain(m)` is the finite domain (of type `Set[K]`) of `m`, i.e., the set of keys it contains. Similarly, `range(m)` denotes the range (or image) of `m`, which has type `Set[V]`.

* map cardinality: `|m|` denotes the cardinality of the map `m`, i.e., the cardinality of its domain.  

* map lookup: If `m` is a map of type `Map[K, V]` and `e` has a type `K`, then `m[e]` looks up the value of key `e` in `m`.  As a well-definedness condition, `e` must be known to be in the domain of `m`, otherwise this expression will result in a verification error.

* map membership: `e in m`, where `m` has type `Map[K, V]` and `e` has type `K`, is true iff `e` is in the domain of `m`.

* map update: If `m` is a map of type `Map[K, V]`, `e1` has type `K` and `e2` has type `V`, then `m[e1 := e2]` is a map that is identical to `m` except the key-value-pair `e1 -> e2` has been added (or its value updated).

### Perm expressions

Expressions of type `Perm` are real numbers and are usually used to represent permission amounts (though they can be used for other purposes).

* Fractional permission expressions `e1/e2`, where both `e1` and `e2` are integers, evaluate to a Perm value whose numerator is `e1` and whose denominator is `e2`. A well-definedness condition is that `e2` must not equal 0. `e1/e2` can also denote a permission amount divided by an integer if `e1` is an expression of type `Perm` and `e2` is an expression of type `Int`.

* The `Perm`-typed literals `none` and  `write` denote no permission and a full permission, corresponding to `0/1` and `1/1`, respectively.

* The special literal `wildcard` denotes an unspecified positive amount. The specific value represented by `wildcard` is not fixed but is chosen anew every time a `wildcard` expression is encountered. In particular, if a `wildcard` amount of permission to a field or predicate is to be exhaled, a value less than the currently held amount is chosen, so that it is always possible to exhale (or assert having) a `wildcard` amount of any permission, unless no permission at all is currently held. However, exhaling and subsequently inhaling a `wildcard` permission to a location will not restore the initial permission amount, since it will not be known that the inhaled `wildcard` amount is equal to the exhaled one. The `wildcard` permission amount provides a convenient way to implement duplicable read-only resources, which, for example, can be used to model immutable data.

* `perm(e.f)`: Evaluates to the amount of permission the current method has to the specified location. Similarly, `perm(P(e1, ..., en))` returns the amount of permission held for the specified predicate instance. Similarly to `forperm`, the values of `perm` expressions take into account the side-effects of e.g. ongoing `exhale` operations. For example `exhale acc(x.f) && perm(x.f) > none` should always fail, while `exhale perm(x.f) > none && acc(x.f)` will succeed (if the full permission to `x.f` was held before the `exhale`).

* Permissions can be added (`e1 + e2`), subtracted (`e1 - e2`), multiplied (`e1 * e2`) or divided (`e1 / e2`). In the first two cases, `e1` and `e2` must both be `Perm`-typed. In the case of multiplication, either two `Perm`-typed expressions or one `Perm`-typed and one `Int`-typed are possible. For divisions, the first expression must be `Perm`-typed and the second of type `Int` (though of course ordinary fractions, where both expressions are `Int`-typed, also exist). The results in all cases will be `Perm`-typed expressions.

### Reference expressions

Reference-typed expressions denote either objects or the special value null (denoted by the `null` literal). The most important fact about `null` is the built-in assertion that permissions to fields of `null` cannot exist; Viper will deduce from holding a field permission that the receiver of the field location is non-null. The analogous assumption does not hold e.g. for predicate instances; it is possible for null to be the value of a predicate parameter.

## Assertions

In addition to expressions, Viper supports three kinds of resource assertions: accessibility predicates for fields, predicate instances, and magic wands.

* boolean expressions: any boolean expression can also be used as an assertion. This includes disjunctions; note, however, that Viper does not support disjunctions whose disjuncts contain resource assertions (such as accessibility predicates). If such a disjunction is desired where *at least one* of the operands is a pure expression, this can be rewritten as a conditional expression.

* Field [permissions](#permissions) are denoted by accessibility predicates `acc(e.f)` and `acc(e.f, p)`, where `e` is an expression of type `Ref`, `f` is a field in the program, and `p` is an expression of type `Perm`, denotes a permission amount of `p` to the field `e.v`. The former is equivalent to writing `acc(e.f, write)`.

* [Predicate instances](#predicates)  can be denoted by `acc(P(...))` and `acc(P(...), p)` (the latter denotes a permission amount `p` of a predicate instance `P(...)`). Where the amount is `write`, the simpler syntax `P(...)` can also be used.

* [Magic wands](#magic-wands) `A1 --* A2` represent the permission to get assertion `A2` in exchange for giving up assertion `A1`.

* Conjunctions `A1 && A2` (similar to the separating conjunction `*` in separation logic); see the section on [fractional permissions](#fractional-permissions).

* Implication `b ==> A`, denotes that assertion `A` holds if the boolean expression `b` is true. Note that only pure expressions may occur on the left of implications, not general assertions.

* [Quantified assertions](#quantified-permissions) `forall x: T :: A`, where `A` is a Viper assertion potentially containing resource assertions, such as accessibility predicates `acc(e.f, p)`.

* Conditional assertions `e ? A1 : A2` denote that `A1` holds if the (pure) boolean expression `e` is true, and otherwise `A2` holds.

* Inhale-exhale assertions `[A1, A2]` behave like `A1` when they are inhaled, but like `A2` when they are exhaled. As an example, `inhale [acc(x.f), acc(x.g)]` is equivalent to `inhale acc(x.f)`. On the other hand, the assertion `[acc(x.f), acc(x.g)]` in a method precondition means that when calling the method, the caller has to give up (exhale) a permission to `x.g`, but when verifying the method body, the verifier inhales permission to `x.f` at the beginning.
