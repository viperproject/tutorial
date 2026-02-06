# Assertion Checking

| Statement | Description |
| ---- | ---- |
| `exhale A` | Check value properties and remove permissions |
| `inhale A` | Add permissions and assume value properties |
| `assert A` | Check permissions and value properties |
| `assume A` | Assume permissions and value properties |
| `refute A` | Refute permissions and value properties |

* `exhale A` and `inhale A` are explained in the [section on permissions](./permissions-inhale-exhale.md).
* `assert A` is similar to `exhale A`, but it does not remove any permissions.
* `assume A` is similar to `inhale A`, but it does not add any permissions.
* `refute A` tries to show that `A` holds for all executions that reach the statement, and causes a verification error if this is the case. In other words, if `A` is provable in some, but not all, execution paths, then the statement still passes.

Note that `inhale acc(...)` adds the given permission to the current state, whereas `assume acc(...)` only keeps executing if the given permission was already in the current state.
