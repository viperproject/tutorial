# Statements {#statements}

This section gives a complete overview of Viper statements. Most of them have
been used throughout this tutorial, but we describe them in more detail here.

## Assignments

Viper supports the following forms of assignments:

| Statement | Description |
| ---- | ---- |
| `x := e`  | Assignment to local variables or result parameters |
| `e1.f := e2` | Assignment to heap locations |
| `x, y := m(...)` | Method calls |
| `x := new(...)` | Object creation |

Assignments to local variables and result parameters of methods work as
expected. It is not possible to assign to input method parameters. Assignment to heap
locations requires the full permission to the heap location (here,
`e1.f`). Methods may have any number of result parameters; method call
statements use the appropriate number (and types) of variables on the left-hand side (using the same variable twice on the left-hand side is disallowed).
A
method call can be understood as an exhale of the method precondition, a reassignment of the variables used to store result parameters, and inhale of the method postcondition.
Finally, a `new` statement creates a new object and inhales exclusive permission
to all (possibly none) fields listed comma-separated within the parentheses. As a special case, `x := new(*)` inhales permission to
*all* fields declared in the Viper program. Note that neither method calls nor
object creation are expressions. Hence, they must not occur as receivers, method
arguments, etc.; instead of nesting these constructs, one typically assigns their results first to local variables, and then uses these.

## Control Structures

Viper supports two main control structures: conditional statements and loops.
Conditional statements have the following form:

```silver
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

```silver
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

```silver-runnable
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

//exercise//

* Strengthen the loop invariant to include exclusive permission to `this.f`. The
  first `assert` statement will now fail to verify because the value of `this.f`
  is no longer framed around the loop
* Adapt the loop invariant such that the `assert` statement verifies again. You
  could use fractional permissions or introduce an additional local variable to
  remember the value of `this.f`
* Add an assignment `x := 3` in the loop body. The second `assert` statement will now fail to
  verify because `x` is now a loop target and, thus, its value is no longer
  framed around the loop
* Strengthen the loop invariant  such that the `assert` statement verifies again.

///

The loop *body* is verified starting from a state that contains no permissions and in
which all loop targets have arbitrary values (all other variables in scope will be known to have the same values as they did immediately before the loop). Verification of the loop body then proceeds as
follows:

1. Inhale the loop invariant and the loop condition `b`;

2. Verify the loop body `S`;

3. Exhale the loop invariant.

Analogous to functions, Viper does also *not* check loop (or method) termination per default, see the [chapter on termination](#termination) for more details. Alternatively, custom termination checks can be encoded through suitable assertions (see the *labelled old expressions* described in the [section on expressions](#expressions)).

## Assertion Checking

| Statement | Description |
| ---- | ---- |
| `exhale A` | Check value properties and remove permissions |
| `inhale A` | Add permissions and assume value properties |
| `assert A` | Check permissions and value properties |
| `assume A` | Assume permissions and value properties |
| `refute A` | Refute permissions and value properties |

* `exhale A` and `inhale A` are explained in the [section on permissions](#inhale-and-exhale).
* `assert A` is similar to `exhale A`, but it does not remove any permissions.
* `assume A` is similar to `inhale A`, but it does not add any permissions.
* `refute A` tries to show that `A` holds for all executions that reach the statement, and causes a verification error if this is the case. In other words, if `A` is provable in some, but not all, execution paths, then the statement still passes.

Note that `inhale acc(...)` adds the given permission to the current state, whereas `assume acc(...)` only keeps executing if the given permission was already in the current state.

## Verifier Directives

| Statement | Description |
| ---- | ---- |
| `unfold P(...)` | Unfold a predicate instance |
| `unfold acc(P(...),p)` | Unfold `p` amount of a predicate instance |
| `fold P(...)`  | Fold a predicate instance |
| `fold acc(P(...),p)` | Fold `p` amount of a predicate instance |
| `package A1 --* A2` | Create a magic wand instance |
| `apply A1 --* A2` | Apply a magic wand instance |

* `unfold` and `fold` are explained in the [section on predicates](#predicates)
* `package` and `apply` are explained in the [section on magic wands](#magic-wands)
* Note that `unfolding` is an [expression](#expressions), not a statement
