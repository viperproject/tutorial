# Boolean expressions

* constants `true` and `false`

* conjunction `e1 && e2`, disjunction `e1 || e2`, implication `e1 ==> e2`. For all cases, both operands are expected to be booleans, and the result will be a boolean. Viper has short-circuiting semantics for these operators, meaning that, for example, in `e1 && e2`, `e2` will only be evaluated if `e1` evaluates to `true`. In particular, this means that `e2` only has to be well-defined if `e1` is true.

* equality `e1 == e2` and inequality `e1 != e2` on all types. Both operands have to be of the same type, and the result is a boolean.

* quantifiers `forall` and `exists`. See the [section on quantifiers](./quantifiers.md) for more details.

* For-perm quantifiers `forperm x: Ref [x.f] :: e`. This expression serves as a quantifier over all objects for which a permission to the specified field is held by the current method. Inside the expression `e` in the body, the variable `x` points to an object for which a positive amount of permission to `x.f` is held. The entire expression is true if `e` is true for every such object, and false otherwise. As an example, `forperm x: Ref [x.g] :: x.g > 0` is true if and only if, for all objects to whose `g`-fields the current method holds a permission, the value of the `g`-field is positive.

`forperm` expressions are useful for implementing leak checks. For example, by asserting `forperm x: Ref [x.f] :: false` we can check that in the current context we do not hold any permission to the field `f`. Note that `forperm` expressions are evaluated in the current heap, including side-effects caused during `exhale` operations, as illustrated in the following example:

```viper
inhale acc(x.f)
exhale forperm x: Ref [x.f] :: false // Would fail because we have acc(x.f)
acc(x.f) && forperm x: Ref [x.f] :: false // Would succeed because we do not have acc(x.f) anymore.
```

This is useful, for example, for checking that after the method postcondition is exhaled, the method body does not have any permission left which would be leaked.

Forperm expressions may not be used in functions or predicates.

* equivalence or bi-implication `e1 <==> e2`, where both expressions are of type `Bool`, is equivalent to writing `e1 == e2`.

* negation `!e`: Negates the boolean expression `e`.

* integer or perm comparisons `e1 < e2`, `e1 <= e2`, `e1 > e2`, `e1 >= e2` require that the operands are either both of type `Int` or both of type `Perm`, and return a `Bool`.
