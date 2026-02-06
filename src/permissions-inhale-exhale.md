# Inhaling and Exhaling

As previously mentioned, accessibility predicates in a method's precondition, such as `acc(x.f)` in the precondition of `inc`, can be understood as specifying that permission to a field (here `x.f`) must be transferred from caller to callee.
The process of gaining permission (which happens in the callee), is called *inhaling* permissions; the opposite process of losing permission (in the caller) is called *exhaling*. Both operations thus update the amount of currently held permissions: from a caller's perspective, permissions required by a precondition are removed before the call and permissions guaranteed by a postcondition are gained after the call returns. From a callee's perspective, the opposite happens.

Similar permission transfers also happen at other points in a Viper program; most notably, when verifying loops: a loop invariant specifies the permissions transferred (1) from the enclosing context to the first loop iteration, (2) from one loop iteration to the next, and (3) from the last loop iteration back to the enclosing context. Inside a loop body, heap locations may only be accessed if the required permissions have been explicitly transferred from the surrounding context to the loop body via the loop invariant.

In addition to specifying which permissions to transfer, Viper assertions may also specify constraints on values, just like in traditional specification languages. For example, a precondition `acc(x.f) && x.f > 0` requires permission to location `x.f` and that its value is positive. Note that the occurrence of `x.f` inside `acc(x.f)` denotes the *location* (in compiler parlance, `x.f` as an lvalue); the meaning of an accessibility predicate is independent of the value of `x.f` as an expression (as used, e.g., in `x.f > 0`).

Consider now the call in the first line of method `client` in the example below: `set`'s precondition specifies that the permission to `a.f` is transferred from the caller to the callee, and that `i` must be greater than `a.f`. Thus, method `client` has to exhale the permission to `a.f` (which is inhaled by `set`) and the caller has to prove that `a.f < i` (which it currently cannot). Conversely, the postcondition causes the permission to be transferred back to the caller when `set` terminates, i.e., it is inhaled by method `client`, and the caller gains the knowledge that `a.f == 5`.
When verifying method `set` itself, the opposite happens: permission to `x.f` is inhaled before the method body is verified, alongside the fact that `x.f < i`. After the body has been verified, permission to `x.f` are exhaled and it is checked that `x.f`'s value is indeed `i`.

```viper,editable,playground
field f: Int

method client(a: Ref)
  requires acc(a.f)
{
  set(a, 5)
  a.f := 6
}

method set(x: Ref, i: Int)
  requires acc(x.f) && x.f < i
  ensures  acc(x.f) && x.f == i
{
  x.f := i
}
```

> **Exercise**
> * Method `client` fails to verify: the precondition of the call `set(a, 5)` may not hold. Can you fix this (without modifying method `set`)?
> * Afterwards, add the following call as the last statement to method `client`: `set(a, a.f)`. Verification will now fail again. Remedy the situation by slightly weakening method `set`'s precondition.
> * Finally, comment out the postcondition of method `set`. Verification will fail again because method `client` does not have permission for the assignment to `a.f`. When a method call terminates, all remaining permissions that are not transferred back to its caller (via its postcondition) are _leaked_ (lost).

Note that when encoding, e.g., a garbage-collected source language into Viper, the design choice that any excess permissions get leaked is convenient; it allows heap-based data to simply go out of scope and become unreachable. However, in the case of `set` in the example above, such leaking is presumably not the intention. Viper can also be used to check that certain permissions are *not* leaked; see the `perm` expression in the [section on expressions](./expressions.md) for more details.

## Inhale and Exhale Statements

To enable the encoding of programming language features that are not directly supported by Viper, such as forking and joining threads or acquiring and releasing locks, Viper allows one to explicitly exhale or inhale permissions via the statements `exhale A` and `inhale A`, where `A` is a Viper assertion such as method `set`'s precondition `acc(x.f) && i < x.f`. From a caller's perspective, `set`'s pre- and postcondition can be seen as syntactic sugar for appropriate exhale and inhale statements before and after a call to the method.

The informal semantics of `exhale A` is as follows:

1. *Assert* that all value constraints in `A` hold; if not, verification fails
1. *Assert* that all permissions denoted (via accessibility predicates) by `A` are currently held; if not, verification fails
1. *Remove* the permissions denoted by `A`

The informal semantics of `inhale A` is as follows:

1. *Add* the permissions denoted by `A` to the program state
1. *Assume* that all value constraints in `A` hold

As an example, consider the following Viper program (ignoring, for the moment, the commented-out lines):

```viper,editable,playground
field f: Int

method set_inex(x: Ref, i: Int) {
  // x.f := i
  inhale acc(x.f)
  x.f := i
  // exhale acc(x.f)
  // x.f := i
}
```

Unlike the previous example, this method has no pre- and postcondition (no `requires`/`ensures`). This means that we start verification of the method body in a state with no permissions. The statement `inhale acc(x.f)` causes the corresponding permission to be added to the state, allowing the assignment on the following line to verify.

> **Exercise**
> * Uncomment the first line of the method body. This will cause a verification error (on that line) since we try to access the location `x.f` before inhaling the necessary permission.
> * Alternatively, uncomment the last two lines of the method body. This will cause a verification error for the last line, since we exhale the permission `x.f` before accessing the heap location.
> * Uncomment the exhale statement and duplicate it, i.e., attempt to exhale permission to `x.f` twice. What happens?
