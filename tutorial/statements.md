# Statements

This section gives a complete overview of Viper statements. Most of them have
been used throughout this tutorial, but we describe them in more detail here.

## Assignments

Viper supports the following forms of assignments:

| Statement | Description |
| ---- | ---- |
| `x := E`  | Assignment to local variables or result parameters |
| `E1.f := E2` | Assignment to heap locations |
| `x, y := m(...)` | Method calls |
| `x := new(...)` | Object creation |

Assignments to local variables and result parameters of methods work as
expected. It is not possible to assign to method parameters. Assignment to heap
locations requires `E1` to be a non-null reference and exclusive permission to
`E1.f`. Methods may have an arbitrary number of result parameters; method call
statements use the appropriate number of variables on the left-hand side. A
method call exhales the method precondition and then inhales its postcondition.
Finally, a `new` statement creates a new object and inhales exclusive permission
to all fields listed within the parantheses. `x := new(*)` inhales permission to
all fields declared in the Viper program. Note that neither method calls nor
object creation are expressions. Hence, they must not occur as receivers, method
arguments, etc.


## Control Structures

Viper supports only two control structures, conditional statements and loops.
Conditional statements have the following form:

```
if(E) {
  S1
} else {
  S2
}
```

where the `else` branch is optional. The semantics is as expected.

Loops have the following form:

```
while(E)
  invariant A
{
  S
}
```

Loops are verified as follows: the code surrounding the loop is verified by
replacing the loop with the following operations: 

1. Exhale the loop invariant;

2. Havoc (assign arbitrary values) to all locals and result parameters that get
assigned to by the loop body `S` (the so-called *loop targets*);

3. Inhale the loop invariant and the negation of the loop condition `E`.

Note that this approach provides two forms of framing: first, locals and result parameters that
are not loop targets are known to be unchanged by the loop. Second, the value of
those heap locations for which the context of the loop holds some permission
that is not transferred into the loop via the loop invariant are also known to
be unchanged. Consequently, it is not necessary to write explicit loop
invariants to preserve information about these variables and locations, as
illustrated by the following example:

```silver {.runnable }
field f: Int
field g: Int

method Foo(this: Ref, n: Int)
  requires acc(this.f) && acc(this.g)
{
  var i: Int := n
  var x: Int := 3
  this.f := 5

  while(0 <= i)
    invariant acc(this.g)
  {
    this.g := this.g + 1
    i := i - 1
  }
  
  exhale this.f == 5
  exhale x == 3
}
```

//exercise//

* Strengthen the loop invariant to include exclusive permission to `this.f`. The
  first `exhale` statement will now fail to verify because the value of `this.f`
  is no longer framed around the loop
* Adapt the loop invariant such that the exhale statement verifies again. You
  could use fractional permissions or introduce an additional local variable to
  remember the value of `this.f`
* Add an assignment `x := 3` in the loop body. The second `exhale` statement will now fail to
  verify because `x` is now a loop target and, thus, its value is no longer
  framed around the loop
* Strengthen the loop invariant  such that the exhale statement verifies again. 

///

The loop itself is verified in a state that contains no permissions and in
which all loop targets have arbitrary values. The verification then proceeds as
follows:

1. Inhale the loop invariant and the loop condition `E`;

2. Verify the loop body `S`;

3. Exhale the loop invariant.

Note that Viper does not enforce termination; if desired, termination checks have to be encoded through
suitable assertions.

## Assertion Checking

| Statement | Description |
| ---- | ---- |
| `exhale A` | Check value properties and remove permissions |
| `inhale A`  | Add permissions and assume value properties |
| `assert A` | Check permissions and value properties |
| `assume E` | Assume value properties |

* `exhale A` and `inhale A` are explained in the 
[section on permissions](#inhale-and-exhale)
* `assert A` is similar to `exhale A`, but does not remove any permissions
* `assume E` is equivalent to `inhale E`; note that it takes an expression rather than an assertion, which must not contain accessibility predicates, predicates, or magic wands

## Verifier Directives

| Statement | Description |
| ---- | ---- |
| `unfold P(...)` | Unfold a predicate instance |
| `fold P(...)`  | Fold a predicate instance |
| `package A1 --* A2` | Create a magic wand instance |
| `apply A1 --* A2` | Apply a magic wand instance |

* `unfold` and `fold` are explained in the [section on predicates](#predicates)
* `package` and `apply` are explained in the [section on magic wands](#magic-wands)
* Note that `unfolding` is an expression, not a statement