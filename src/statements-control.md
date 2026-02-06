# Control Structures

Viper supports two main control structures: conditional statements and loops.
Conditional statements have the following form:

```viper
if (E1) {
  S1
} elseif (E2) {
  S2
} else {
  S3
}
```

where there may be any number of `elseif` branches (including none), and the `else` branch is optional. The semantics is as expected.

Loops have the following form:

```viper
while (b)
  invariant A
{
  S
}
```

Loops are verified as follows: with respect to the scope *surrounding* the loop, verification amounts to replacing the loop with the following operations:

1. Exhale the loop invariant;

2. Havoc (assign arbitrary values) to all locals and result parameters that get assigned to by the loop body `S` (the so-called *loop targets*);

3. Inhale the loop invariant and the *negation* of the loop condition `b`; the verification of any code following the loop proceeds from this state.

Note that this approach provides two forms of framing: first, locals and result parameters that
are *not* loop targets are always known to be unchanged by the loop. Second, the value of
those heap locations for which the context of the loop holds some permission
that is *not* transferred into the loop via the loop invariant are also known to
be unchanged. Consequently, it is not necessary to write explicit loop
invariants to preserve information about these variables and locations, as is
illustrated by the following example:

```viper,editable,playground
field f: Int
field g: Int

method Foo(this: Ref, n: Int)
  requires acc(this.f) && acc(this.g)
{
  var i: Int := n
  var x: Int := 3
  this.f := 5

  while (0 <= i)
    invariant acc(this.g)
  {
    this.g := this.g + 1
    i := i - 1
  }
  
  assert this.f == 5
  assert x == 3
}
```

> **Exercise**
> * Strengthen the loop invariant to include exclusive permission to `this.f`. The
>   first `assert` statement will now fail to verify because the value of `this.f`
>   is no longer framed around the loop
> * Adapt the loop invariant such that the `assert` statement verifies again. You
>   could use fractional permissions or introduce an additional local variable to
>   remember the value of `this.f`
> * Add an assignment `x := 3` in the loop body. The second `assert` statement will now fail to
>   verify because `x` is now a loop target and, thus, its value is no longer
>   framed around the loop
> * Strengthen the loop invariant  such that the `assert` statement verifies again.

The loop *body* is verified starting from a state that contains no permissions and in
which all loop targets have arbitrary values (all other variables in scope will be known to have the same values as they did immediately before the loop). Verification of the loop body then proceeds as
follows:

1. Inhale the loop invariant and the loop condition `b`;

2. Verify the loop body `S`;

3. Exhale the loop invariant.

Analogous to functions, Viper does also *not* check loop (or method) termination per default, see the [chapter on termination](./termination.md) for more details. Alternatively, custom termination checks can be encoded through suitable assertions (see the *labelled old expressions* described in the [section on expressions](./expressions-multi.md)).
