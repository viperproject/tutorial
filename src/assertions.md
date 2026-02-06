# Assertions

In addition to expressions, Viper supports three kinds of resource assertions: accessibility predicates for fields, predicate instances, and magic wands.

* boolean expressions: any boolean expression can also be used as an assertion. This includes disjunctions; note, however, that Viper does not support disjunctions whose disjuncts contain resource assertions (such as accessibility predicates). If such a disjunction is desired where *at least one* of the operands is a pure expression, this can be rewritten as a conditional expression.

* Field [permissions](./permissions.md) are denoted by accessibility predicates `acc(e.f)` and `acc(e.f, p)`, where `e` is an expression of type `Ref`, `f` is a field in the program, and `p` is an expression of type `Perm`, denotes a permission amount of `p` to the field `e.v`. The former is equivalent to writing `acc(e.f, write)`.

* [Predicate instances](./predicates.md)  can be denoted by `acc(P(...))` and `acc(P(...), p)` (the latter denotes a permission amount `p` of a predicate instance `P(...)`). Where the amount is `write`, the simpler syntax `P(...)` can also be used.

* [Magic wands](./magic-wands.md) `A1 --* A2` represent the permission to get assertion `A2` in exchange for giving up assertion `A1`.

* Conjunctions `A1 && A2` (similar to the separating conjunction `*` in separation logic); see the section on [fractional permissions](./permissions-fractional.md).

* Implication `b ==> A`, denotes that assertion `A` holds if the boolean expression `b` is true. Note that only pure expressions may occur on the left of implications, not general assertions.

* [Quantified assertions](./quantified-permissions.md) `forall x: T :: A`, where `A` is a Viper assertion potentially containing resource assertions, such as accessibility predicates `acc(e.f, p)`.

* Conditional assertions `e ? A1 : A2` denote that `A1` holds if the (pure) boolean expression `e` is true, and otherwise `A2` holds.

* Inhale-exhale assertions `[A1, A2]` behave like `A1` when they are inhaled, but like `A2` when they are exhaled. As an example, `inhale [acc(x.f), acc(x.g)]` is equivalent to `inhale acc(x.f)`. On the other hand, the assertion `[acc(x.f), acc(x.g)]` in a method precondition means that when calling the method, the caller has to give up (exhale) a permission to `x.g`, but when verifying the method body, the verifier inhales permission to `x.f` at the beginning.
