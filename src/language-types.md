# Built-in types

* `Ref` for references (to objects, except for the built-in `Ref` constant `null`)
* `Bool` for Boolean values
* `Int` for mathematical (unbounded) integers
* `Rational` for mathematical (unbounded) rationals (this type is expected to be deprecated in the summer 2023 release)
* `Perm` for permission amounts (see the [section on permissions](./permissions.md) for details)
* `Seq[T]` for immutable sequences with element type `T`
* `Set[T]` for immutable sets with element type `T`
* `Multiset[T]` for immutable multisets with element type `T`
* `Map[T, V]` for immutable maps with key type `T` and value type `V`
* Additional types can be defined via [domains](./domains.md)
