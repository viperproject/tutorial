# Fractional Permissions

Exclusive permissions are too restrictive for some applications. For instance, it is typically safe for multiple threads of a source program to concurrently access the same heap location as long as all accesses are reads. That is, read access can safely be shared. However, if any thread potentially writes to a heap location, no other should typically be allowed to concurrently read it (otherwise, the program has a *data race*). To support encoding such scenarios, Viper also supports *fractional permissions* with a *permission amount* between 0 and 1. Any non-zero permission amount allows read access to the corresponding heap location, but only the exclusive permission (1) allows modifications.

The general form of an accessibility predicate for field permissions is `acc(e.f, p)`, where `e` is a `Ref`-typed expression, `f` is a field name, and `p` denotes a permission amount. Permission amounts are denoted by `write` for exclusive permissions, `none` for zero permission, quotients of two `Int`-typed expressions `i1/i2` to denote a fractional permission; any `Perm`-typed expression may be used here. `Perm` is the type of permission amounts, which is a built-in type that can be used like any other type. The permission amount parameter `p` is optional and defaults to `write`. For example, `acc(e.f)`, `acc(e.f, write)` and `acc(e.f, 1/1)` all have the same meaning.

The next example illustrates the usage of fractional permissions to distinguish between read and write access: there, method `copyAndInc` requires write permission to `x.f`, but only read permission (we arbitrarily chose `1/2`, but any non-zero fraction would suffice) to `y.f`.

```viper,editable,playground
field f: Int

method copyAndInc(x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f, 1/2)
  ensures  acc(x.f) && acc(y.f, 1/2)
{
  x.f := y.f + 1
}
```

> **Exercise**
> * Change the permission amount for `x.f` to `9/10`, i.e., the corresponding accessibility predicates to `acc(x.f, 9/10)`. Where does the code fail (and why)?
> * Alternatively, change the implementation to `y.f := x.f + 1`.
> * Revert to the original example. Afterwards, change the permission amount for `y.f` to `none` (or `0/1`). Where does the code fail (and why)?

Fractional permissions to the same location are *summed up*: inhaling `acc(x.f, p1) && acc(x.f, p2)` is equivalent to inhaling `acc(x.f, p1 + p2)`, and analogously for exhaling. As before, inhaling permissions maintains the invariant that write permission to a location are exclusive. With fractional permission in mind, this can be rephrased as maintaining the invariant that the permission amount to a location never exceeds 1.

To illustrate this, consider the next example (and its exercises): there, the `assert` statement fails because holding one third permission to each `x.f` and `y.f` does not imply that `x` and `y` cannot be aliases, since the sum of the individual permission amounts does not exceed 1.

```viper,editable,playground
field f: Int

method test(x: Ref, y: Ref) {
  inhale acc(x.f, 1/2) && acc(y.f, 1/2)
  assert x != y
}
```

> **Exercise**
> * Change both permission amounts to `2/3`. The `assert` statement will now verify.
> * Revert to the original example. Afterwards, replace the `assert` statement by `inhale x == y` and add the statement `exhale acc(x.f, 1/1)` to the end of method `test`. The code verifies, which illustrates that permission amounts are summed up.
> * Revert to the original example. Afterwards, replace the `assert` statement by `exhale acc(x.f, 1/8) && acc(x.f, 1/8)`, and add the subsequent statement `exhale acc(x.f, 1/4)`. The code verifies, which illustrates that permission amounts can be split up.
> * Revert to the original example. Afterwards, add a third argument `z: Ref` to the signature of method `test`, add the conjunct `acc(z.f, 1/2)` to the `inhale` statement and change the `assert` statement to `x != y || x != z`. This verifies , but neither disjunct on their own will. Why?

While fractional permissions no longer always guarantee non-aliasing between references, as demonstrated by the previous example, they still enable framing, e.g., across method calls: from a caller's perspective, holding on to a non-zero permission amount to a location `x.f` across a method call guarantees that the value of `x.f` cannot be affected by the call. That is, because the callee would need to obtain write permission, i.e., permission amount 1, which cannot happen as long as the caller retains its fraction.

The next example illustrates the use of fractional permissions for framing: there, method `client` can frame the property `b.f == 3` across the call to `copyAndInc` because `client` retains half the permission to `b.f` across the call. Note that the postcondition of `copyAndInc` does not explicitly state that the value of `y.f` remains unchanged.

```viper,editable,playground
field f: Int

method copyAndInc(x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f, 1/2)
  ensures  acc(x.f) && acc(y.f, 1/2)
  ensures  x.f == y.f + 1
{
  x.f := y.f + 1
}

method client(a: Ref, b: Ref) {
  inhale acc(a.f) && acc(b.f)

  a.f := 1
  b.f := 3

  copyAndInc(a, b)

  assert b.f == 3 && a.f == 4
}
```

> **Exercise**
> * Add the statement `exhale acc(b.f, 1/2)` right before the invocation of `copyAndInc`. Since method `client` temporarily loses all permission to `b.f`, the property `b.f == 3` can no longer be framed across the call. Note that method `client` cannot deduce modularly (i.e., without considering the body of method `copyAndInc`) that `copyAndInc` does *not* modify `b.f`; the method body might inhale the other half permission (e.g., modelling the acquisition of a lock) and thus, be able to assign to `b.f`.
> * Can you fix the new code by changing the specifications of method `copyAndInc`?
> * Revert to the original example. Afterwards, modify method `client` as follows: change the invocation of method `copyAndInc` to `copyAndInc(a, a)`, and change the `assert` statement to `assert b.f == 3 && a.f == 2`. To verify the resulting code, you'll have to change the specifications of method `copyAndInc`.
> * Can you find specifications for method `copyAndInc` that allow verifying both versions of method `client`: the original implementation (`copyAndInc(a, b); assert b.f == 3 && a.f == 4`) and the new one (`copyAndInc(a, a); assert b.f == 3 && a.f == 2`). That is, can you find specifications that work, regardless of whether or not the passed references are aliases?
