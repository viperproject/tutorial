# Expressions and Assertions

## Expressions ##

Viper supports a number of different kinds of expressions, which can be evaluated to a value of one of the types supported in Viper.

The primitive types supported in Viper are booleans, integers, permission amounts (rational numbers) and references to heap objects. In addition, there are built-in set, multiset and sequence types, and users can define custom types using domains.

Evaluating an expression never changes the state of the program, i.e., expression evaluation has no side effects. However, expression evaluation comes with well-definedness conditions for some expressions: evaluating an expression can cause a verification failure if the expression is not well-defined in the current program state; this leads to a verification error. As an example, the expression `x % y` is not well-defined if `y` is equal to zero, and the expression `o.f` is only well-defined if `o` is not `null` and the current method has the permission to read `o.f`.

In the following, we list the different kinds of expressions, remark on their well-definedness and the value they evaluate to.

### Expressions of multiple types:

*   field access `e.f`: requires at least some permission to read the field location; returns a value of the type of the field.

*   function application `f(...)`: The function can either be a domain function or a normal, heap dependent function. In the latter case, the function's precondition must be fulfilled, and in both cases, the argument expressions must be well-defined and have the expected types. Evaluates to a value of the type of the function. See the respective sections for more information on [functions](#functions) and [domains](#domains).

*   local variable and parameter access: read the current value of the named variable or parameter. Note that it is possible to read local variables which have not been assigned to; in this case, the expression will evaluate to an arbitrary value of its type.

*   conditional expressions `e1 ? e2 : e3`, where `e1` has type `Bool` and `e2` and `e3` must have the same type; evaluates to `e2` if `e1` is `true`, and otherwise to `e3`.

*   `unfolding acc(P(...), p) in e`: Requires that the current method has at least the permission amount `p` to the predicate `P(...)`. Evaluates `e` in a context where `P` has been temporarily unfolded (i.e., `P` is no longer available, but its contents are).

*   `old(e)`, `old[l](e)`: Evaluates expression `e` in an old heap. In the first case, this is the heap at the start of the current method call, in the second, it is the heap at the position of the label `l`. For the second expression to be well-defined, the label `l` must be in the same method as the old-expression, and must have been encountered by the time the old-expression is evaluated; as a result, old-expressions cannot be used in functions, predicates or preconditions (they also cannot be used in postconditions but for a different reason: they would be meaningless for the caller). Note that `old` does not affect the value of variable references; `old(x.f)`, for example, evaluates to the value that the field `f` of the object that the variable `x` **currently** points to had at the beginning of the method.

*   `result`: Can only be used in postconditions of heap-dependent functions, and refers to the result of the function application; it therefore has the type of the function it belongs to.

*   `let v := (e1) in e2`: Evaluates `e1`, and subsequently evaluates `e2` in a context where the variable `v` is bound to the value of `e1` (currently, the parentheses are necessary). The let expressions are often convenient when one needs to write an expression that is evaluated in several states. For example, if it is needed to evaluate the argument of a function call `f(x.f)` in a current state and the function itself in an old state, it can be expressed by using a let expression as follows: `let x_f := (x.f) in old(f(x_f))`.

### Integer expressions:

*   constants, e.g. `-2`, `1023123909`. Integers in Viper are signed and unbounded.

*   unary minus `-e`: Negates the value of `e` if `e` is itself an integer.

*   addition, subtraction, multiplication, division, modulo (`e1 + e2`, `e1 - e2`, `e1 * e2`, `e1 \ e2`, `e1 % e2`). For all of them, both operands are expected to be integers, and the result will be an integer. Note the unusual syntax for the division operator: Alternatively, the more widespread operator  `/` can be used, but it will only perform integer division if the context determines that the result must be an integer (e.g., if the result is assigned to a local variable of type `Int`); otherwise, the result will be an expression of type `Perm`.

### Boolean expressions:

*   constants `true`, `false`

*   conjunction `e1 && e2`, disjunction `e1 || e2`, implication `e1 ==> e2`. For all cases, both operands are expected to be booleans, and the result will be a boolean. Viper has short-circuit semantics for these operators, meaning that, for example, in `e1 && e2`, `e2` will only be evaluated if `e1` evaluates to `true`. In particular, this means that `e2` only has to be well-defined if `e1` is true.

*   equality `e1 == e2` and inequality `e1 != e2` on all types. Both operands have to be of the same type, and the result is a boolean.

*   quantifiers `forall` and `exists`. See the [section on quantifiers](#quantifiers) for more details.

*   `forperm x: Ref [x.f] :: e`: This expression serves as a quantifier over all objects for which a permission to the specified field is held by the current method. Inside the expression `e` in the body, the variable `x` points to an object for which a positive amount of permission to `x.f` is held. The entire expression is true if `e` is true for every such object, and false otherwise. As an example, `forperm r: Ref [r.g] :: r.g > 0` is true if and only if, for all objects to whose `g`-fields the current method holds a permission, the value of the `g`-field is positive.

    `forperm` expressions are useful for implementing leak checks. For example, by asserting `forperm x: Ref [x.f] :: false` we can check that in the current context we do not hold any permission to the field `f`. Note that `forperm` expressions are evaluated in the currently evaluated heap as illustrated by the following example:

    ```silver
    inhale acc(x.f)
    exahle forperm x: Ref [x.f] :: false && // Would fail because we have acc(x.f)
           acc(x.f) &&
           forperm x: Ref [x.f] :: false    // Would succeed because we do not have acc(x.f) anymore.
    ```

    This is useful, for example, for checking that after the method postcondition is exhaled, the method body does not have any permission left which would be leaked.

    Forperm expressions must not be used in functions or predicates.

*   equivalence or biimplication `e1 <==> e2`, where both expressions are of type `Bool`, is equivalent to writing `e1 == e2`.

*   negation `!e`: Negates the boolean expression `e`.

*   integer or perm comparisons `e1 < e2`, `e1 <= e2`, `e1 > e2`, `e1 >= e2` require that the operands are either both of type `Int` or both of type `Perm`, and return a `Bool`.

### Set expressions

Viper has a built-in parametric finite set type `Set[T]`, where `T` is a type parameter that describes the type of the elements of the set. Sets are immutable (i.e. represent mathematical sets).

* empty set: `Set[T]()` returns an empty set of type `Set[T]`. The type argument `T` is optional if the type is clear from the context; then simply `Set()` can be written.

* set literals: `Set(e1, e2, ..., en)` evaluates to a set containing only the n enumerated values and have the type `Set[T]`, where `T` is the common type of the enumerated expressions.

* `e1 union e2`, `e1 intersection e2`, `e1 setminus e2` perform the respective set operations. In all cases, `e1` and `e2` must be sets of the same type, and the entire expression has the same type as its operands. These operators each define a set; the operand sets will not be modified (Viper sets are not mutable).

* `e1 subset e2` has type `Bool` and evaluates to `true` if and only if `e1` is a subset of `e2`. Again, both operands have to be sets of the same type.

* Similarly, `e1 in e2`, where `e2` has the type `Set[T]` for some `T` and `e1` has type `T`, evaluates to true if and only `e1` is a member of `e2`.

* set cardinality `|s|` evaluates to a non-negative integer that represents the cardinality of `s`.

Similar to sets, Viper supports multisets:

* Literals can either be empty multisets (`Multiset[T]()`) or non-empty ones (`Multiset(e, ...)`) and work like their set counterparts.

* As for sets, the operations `union`, `intersection`, `setminus`, `subset` and cardinality `|s|` are supported.

### Sequence expressions {#sequences}

Viper's built-in sequence type `Seq[T]` represents an immutable, finite sequence of elements of type `T`.

* empty sequence: `Seq[T]()` evaluates to an empty sequence of type `Seq[T]`. Like with empty set literals, the type argument has to be stated explicitly.

* sequence literal: `Seq(e1, e2, ..., en)`, where `e1`-`en` are expressions that all have a common type `T`, represents a sequence of type `Seq[T]` of `n` elements, whose elements are the argument expressions (i.e., the first element is `e1`, the second `e2` etc., and the last is `en`.

* integer sequence literals `[e1..e2]`, where `e1` and `e2` are integers, represent the sequence of integers ranging from `e1` until, but excluding, `e2` (or the empty sequence, if `e2` is less than `e1`).

* sequence lookup `s[e]`, where `s` is an expression of type `Seq[T]` for some `T` and `e` is an integer, returns the element at index `e` in the sequence. `e` must be known to be non-negative and less than the length of `s`, otherwise this expression will result in a verification error.

* sequence concatenation `e1 ++ e2` results in a new sequence whose elements are the elements of `e1`, followed by those of `e2`.

* A sequence update `s[e1 := e2]`, where `e1` has type `Int`, `s` has type `Seq[T]` for some `T` and `e2` is of type `T`, denotes the sequence that is identical to `s`, except that the element at index `e1` is `e2` (the operation does not change the original sequence's value, but rather defines a new sequence).

* sub-sequence operations: `s[e1..e2]`, where `s` is a sequence and `e1` and `e2` are integers, returns a new sequence that contains the elements of `s` starting from index `e1` until (i.e., not including) index `e2`. Optionally, either the first or the second index can be left out (leading to expressions of the form `s[..e]` and `s[e..]`), in which case only elements at the end or at the beginning of `s` are dropped, respectively. If any given index is outside the range of `s`, or the given range would be negative, an empty sequence will be returned; this will not result in a verification error.

* sequence length (`|s|`) returns the length of a sequence as an integer.

### <a name="perm-expressions"></a>Perm expressions

Expressions of type `Perm` are rational numbers and are usually used to represent permission amounts (though they can be used for other purposes).

*   Fractional permission expressions `e1/e2`, where both `e1` and `e2` are integers, evaluate to a Perm value whose numerator is `e1` and whose denominator is `e2`. A well-definedness condition is that `e2` must not equal 0. `e1/e2` can also denote the permission division by an integer if `e1` is an expression of type `Perm` and `e2` is an expression of type `Int`.

*   The perm literals `none` and  `write` denote no permission and a full permission, corresponding to `0/1` and `1/1`, respectively.

*   The special literal `wildcard` denotes an unspecified positive amount. The specific value represented by `wildcard` is not fixed but is chosen anew every time a `wildcard` expression is encountered. In particular, if a `wildcard` amount of permission to a field or predicate is to be exhaled, a value less than the currently held amount is chosen, so that it is always possible to exhale (or assert having) a `wildcard` amount of any permission, unless no permission at all is currently held. However, exhaling and subsequently inhaling a `wildcard` permission to a location will not restore the initial permission amount, since it will not be known that the inhaled `wildcard` amount is equal to the exhaled one. The `wildcard` permission amount provides a convenient way to implement duplicable read-only resources, which, for example, can be used to model immutable data.

*   `perm(e.f)`: Evaluates to the amount of permission the current method has to the specified location. Similarly, `perm(P(e1, ..., en))` returns the amount of permission held for the specified predicate instance. Similarly to `forperm`, `perm` is always evaluated in the current heap.

*   Permissions can be added (`e1 + e2`), subtracted (`e1 - e2`), or multiplied (`e1 * e2`). In all cases, `e1` has to be a permission expression, `e2` has to be another permission expression in the first two cases and can be either an integer or a permission expression in the last case, and the result will be a permission expression.

### Reference expressions

References are created using the `new` statement (see [section on assignments](#assignments)). There is only one pre-existing reference expression, namely the `null` literal. The most important fact about `null` is the built-in assertion that permissions to fields of `null` cannot exist; Viper will deduce from holding a field permission that the receiver of the field location is non-null.

## Assertions ##

In addition to expressions, Viper supports three resource assertions: accessibility predicates for fields, predicate instances, and magic wands.

* boolean expressions: any boolean expression can also be used as an assertion. This includes disjunctions; note, however, that Viper does not support disjunctions whose disjuncts contain resource assertions (such as accessibility predicates).

* Field [permissions](#permissions) are denoted by accessibility predicates `acc(e.f)` and `acc(e.f, p)`, where `e` is an expression of type `Ref`, `f` is a field in the program, and `p` is an expression of type `Perm`, denotes a permission amount of `p` to the field `e.v`. The former is equivalent to writing `acc(e.f, write)`.

* [Predicate instances](#predicates)  can be denoted by `acc(P(...))` and `acc(P(...), p)` (the latters denotes a permission amount `p` of a predicate instance `P(e, ...)`). Where the amount is `write`, the simpler syntax `P(...)` can also be used.

* [Magic wands](#magic-wands) `A1 --* A2` represent the permission to get assertion `A2` in exchange for giving up assertion `A1`.

* Conjunctions `A1 && A2` (similar to the separating conjuction `*` in separation logic); see the section on [fractional permissions](#fractional-permissions).

* Implication `b ==> A`, denotes that assertion `A` holds if the boolean expression `b` is true. Note that only expressions may occur on the left of implications, not general assertions.

* [Quantified assertions](#quantified-permissions) `forall x: T :: A`, where `A` is a Viper assertion potentially containing resource assertions, such as accessibility predicates `acc(e.f, p)`.

* Conditional assertions `e ? A1 : A2` denote that `A1` holds if the boolean expression `e` is true, and otherwise `A2` holds.

* Inhale-exhale assertions `[A1, A2]` behave like `A1` when they are inhaled, but like `A2` when they are exhaled. As an example, `inhale [acc(x.f), acc(x.g)]` is equivalent to `inhale acc(x.f)`. On the other hand, the assertion `[acc(x.f), acc(x.g)]` in a method precondition means that when calling the method, the caller has to give up (exhale) a permission to `x.g`, but when verifying the method body, the verifier inhales permission to `x.f` at the beginning.