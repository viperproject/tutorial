# Verifier Directives

| Statement | Description |
| ---- | ---- |
| `unfold P(...)` | Unfold a predicate instance |
| `unfold acc(P(...),p)` | Unfold `p` amount of a predicate instance |
| `fold P(...)`  | Fold a predicate instance |
| `fold acc(P(...),p)` | Fold `p` amount of a predicate instance |
| `package A1 --* A2` | Create a magic wand instance |
| `apply A1 --* A2` | Apply a magic wand instance |

* `unfold` and `fold` are explained in the [section on predicates](./predicates.md)
* `package` and `apply` are explained in the [section on magic wands](./magic-wands.md)
* Note that `unfolding` is an [expression](./expressions.md), not a statement
