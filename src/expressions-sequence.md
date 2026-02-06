# Sequence expressions

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
